#!/usr/bin/env python3
"""Gate real solvers at a two-party check barrier; never race using delays."""
import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import threading


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def wrapper(root, backend):
    config = json.loads((root / "config.json").read_text())
    if any(argument in ("-version", "--version") for argument in sys.argv[1:]):
        os.execv(config[backend], [config[backend], *sys.argv[1:]])
    real = subprocess.Popen([config[backend], *sys.argv[1:]], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, text=True, bufsize=1)
    canonical = []
    active = None
    lock = threading.Lock()

    def forward():
        for line in real.stdout:
            with lock:
                if active is not None:
                    with active.with_suffix(".out").open("a") as log:
                        log.write(line)
            sys.stdout.write(line)
            sys.stdout.flush()

    reader = threading.Thread(target=forward)
    reader.start()
    try:
        for line in sys.stdin:
            command = line.strip()
            if command.startswith("(check-sat"):
                with socket.create_connection(("127.0.0.1", config["port"])) as connection:
                    request = {"backend": backend, "pid": os.getpid(),
                               "canonical": canonical, "check": command}
                    connection.sendall((json.dumps(request) + "\n").encode())
                    reply = connection.makefile("r").readline()
                    require(bool(reply), "check barrier closed before releasing winner")
                    with lock:
                        active = root / reply.strip()
            elif command.startswith("(get-model") or command.startswith("(get-value"):
                require(active is not None, "model query before a current check")
                with active.open("a") as log:
                    log.write(line)
            elif command != "(exit)":
                canonical.append(command)
            real.stdin.write(line)
            real.stdin.flush()
            if command == "(exit)":
                break
    finally:
        # Outer Lean and these solvers have different process groups. A closed
        # barrier must retire the real child even after the Lean owner has died.
        if real.poll() is None:
            real.terminate()
            try:
                real.wait(timeout=2)
            except subprocess.TimeoutExpired:
                real.kill()
                real.wait(timeout=2)
        try:
            real.stdin.close()
        except BrokenPipeError:
            pass
        reader.join(timeout=2)
        require(not reader.is_alive(), "solver output reader survived retirement")
        real.stdout.close()
    sys.exit(real.returncode)


def serve(root, mode):
    server = socket.socket()
    server.bind(("127.0.0.1", 0))
    server.listen()
    config = {backend: shutil.which(backend) for backend in ("z3", "cvc5")}
    require(all(config.values()), "both real solvers must be available")
    config["port"] = server.getsockname()[1]
    (root / "config.json").write_text(json.dumps(config))
    fixture = str(Path(__file__).resolve())
    for backend in ("z3", "cvc5"):
        script = root / backend
        script.write_text(f"#!{sys.executable}\nimport runpy\n"
                          f"ns = runpy.run_path({fixture!r})\n"
                          f"ns['wrapper'](ns['Path']({str(root)!r}), {backend!r})\n")
        script.chmod(0o755)
    rounds = {}
    counts = {"z3": 0, "cvc5": 0}
    held = []
    failures = []

    def accept():
        try:
            while True:
                connection, _ = server.accept()
                request = json.loads(connection.makefile("r").readline())
                backend = request["backend"]
                counts[backend] += 1
                number = counts[backend]
                pair = rounds.setdefault(number, {})
                pair[backend] = (request, connection)
                if len(pair) != 2:
                    continue
                winner = "z3" if number % 2 else "cvc5"
                for name, (item, channel) in pair.items():
                    stem = f"{number}-{name}"
                    (root / f"{stem}.smt2").write_text(
                        "\n".join(item["canonical"] + [item["check"]]) + "\n")
                    if name == winner:
                        channel.sendall(f"{stem}.smt2\n".encode())
                        channel.close()
                    else:
                        held.append(channel)
        except Exception as error:
            failures.append(str(error))

    threading.Thread(target=accept, daemon=True).start()
    print("ready", flush=True)
    require(sys.stdin.readline().strip() == "finish", "missing finish handshake")
    require(not failures, f"barrier failed: {failures}")
    require(counts["z3"] == counts["cvc5"] and counts["z3"] >= 3,
            f"expected at least three paired checks, got {counts}")
    previous = None
    manifest = []
    checks = []
    model_count = 0
    for number, pair in sorted(rounds.items()):
        winner = "z3" if number % 2 else "cvc5"
        request = pair[winner][0]
        checks.append(request["check"])
        if previous is not None:
            # Last round's loser must have been retired and actually respawned.
            loser = winner
            require(pair[loser][0]["pid"] != previous[loser][0]["pid"],
                    f"round {number}: retired {loser} was not restarted")
        previous = pair
        canonical = lambda item: [line for line in item["canonical"]
                                  if not line.startswith("(set-")]
        require(canonical(pair["z3"][0]) == canonical(pair["cvc5"][0]),
                f"round {number}: restarted canonical declarations/assertions diverged")
        require(pair["z3"][0]["check"] == pair["cvc5"][0]["check"],
                f"round {number}: backend assumptions diverged")
        require(any(line.startswith("(declare-") for line in request["canonical"]),
                f"round {number}: goal had no declarations")
        require(any(line.startswith("(assert ") for line in request["canonical"]),
                f"round {number}: goal had no assertions")
        if mode == "kind":
            require(any(line.startswith("(declare-") and "_InitFlag" in line
                        for line in request["canonical"]),
                    f"round {number}: restarted kind session lost the init declaration")
            require(any(line.startswith("(assert ") and "_InitFlag" in line
                        for line in request["canonical"]),
                    f"round {number}: restarted kind session lost the guarded initialization")
        for backend in ("z3", "cvc5"):
            stem = f"{number}-{backend}"
            path = root / f"{stem}.smt2"
            text = path.read_text()
            require(sum(line.startswith("(check-sat") for line in text.splitlines()) == 1,
                    f"{stem}: stale check in current transcript")
            models = sum(line.startswith("(get-") for line in text.splitlines())
            if backend != winner:
                require(models == 0, f"{stem}: retired loser received model work")
            else:
                model_count += models
            with path.open("a") as log:
                log.write("(exit)\n")
            manifest.append(f"{backend} {stem} {number}-{winner}")
    require(all(check.startswith("(check-sat-assuming") for check in checks),
            f"unexpected checks: {checks}")
    if mode == "bmc":
        require(len(set(checks)) >= 3, "BMC did not reach three distinct depth assumptions")
    elif mode == "kind":
        require(len(checks) >= 4 and any("(not " in check for check in checks),
                "kind did not submit both base and induction checks")
        for base, step in zip(checks[::2], checks[1::2]):
            require("_InitFlag" in base and "_InitFlag" in step and
                    "(not " not in base and "(not " in step,
                    f"kind base/step init polarity did not alternate: {base}, {step}")
        require(model_count > 0, "kind induction counterexamples omitted current model queries")
    else:
        require(len(checks) == 3 and checks[0] == checks[2] != checks[1],
                f"evidence checks did not alternate assumptions: {checks}")
        require(model_count == 3, f"expected one current model query per check, got {model_count}")
    (root / "manifest").write_text("\n".join(manifest))
    print("finished", flush=True)
    for connection in held:
        connection.close()
    server.close()


def normalized(text):
    return " ".join(line.strip() for line in text.splitlines()
                    if line.strip() and line.strip() != "success")


def compare(root, mode):
    verdicts = []
    for row in (root / "manifest").read_text().splitlines():
        backend, stem, winner = row.split()
        current = normalized((root / f"{winner}.out").read_text())
        fresh = normalized((root / f"{stem}.fresh").read_text())
        verdict = current.split()[0]
        require(verdict in ("sat", "unsat"), f"{winner}: no real solver verdict: {current}")
        require(fresh.split()[0] == verdict and "error" not in fresh,
                f"{stem}: fresh replay differs: current={current}, fresh={fresh}")
        if stem == winner:
            verdicts.append(verdict)
            if mode == "evidence":
                require(current == fresh, f"{stem}: stale model: {current} != {fresh}")
    if mode == "bmc":
        require(all(verdict == "unsat" for verdict in verdicts), f"BMC verdicts: {verdicts}")
    elif mode == "kind":
        require(verdicts[::2] == ["unsat"] * len(verdicts[::2]) and
                verdicts[1::2] == ["sat"] * len(verdicts[1::2]), f"kind phases: {verdicts}")
    else:
        require(verdicts == ["sat", "sat", "sat"], f"evidence verdicts: {verdicts}")
    print("verified", flush=True)


if __name__ == "__main__":
    action, directory, mode = sys.argv[1:]
    if action == "serve":
        serve(Path(directory), mode)
    elif action == "compare":
        compare(Path(directory), mode)
    else:
        raise RuntimeError(f"unknown fixture action: {action}")
