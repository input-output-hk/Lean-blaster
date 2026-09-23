#!/bin/sh
# Mode-selected adversarial solver. Marker files acknowledge actual transitions;
# no scenario relies on a sleep to order solver responses.
mode=$1
directory=$2
verdict=${3:-unsat}
trap '' TERM
printf '%s\n' "$$" > "$directory/leader.pid"
exec 3<&0

case "$mode" in
  silent) printf 'SILENT_PROTOCOL_DIAGNOSTIC\n' >&2 ;;
  cleanup-cancel)
    trap ': > "$directory/term-requested"; while [ ! -f "$directory/cancel-issued" ]; do sleep 0.01; done' TERM
    ;;
  session)
    backend=$verdict
    shift 3
    case "$1" in
      -version|--version)
        if [ "$backend" = cvc5 ] && [ "$BLASTER_TEST_STAGE" = restart-probe ] &&
            [ -f "$directory/cvc5.count" ]; then
          : > "$directory/blocked"
          echo "deliberate restart probe failure" >&2
          exit 17
        fi
        printf '%s version 4.15.4\n' "$backend"; exit 0 ;;
    esac
    count=0
    if [ -f "$directory/$backend.count" ]; then read -r count < "$directory/$backend.count"; fi
    count=$((count + 1))
    printf '%s\n' "$count" > "$directory/$backend.count"
    printf '%s\n' "$$" > "$directory/$backend-$count.pid"
    while IFS= read -r line; do
      if [ "$backend" = cvc5 ] && [ "$BLASTER_TEST_STAGE" = paced-setup ] &&
          [ "$line" != '(exit)' ]; then
        # Each acknowledgement is healthy; the complete setup exceeds one operation budget.
        : > "$directory/blocked"
        sleep 1
        echo success
        continue
      fi
      if [ "$backend" = cvc5 ] &&
          { [ "$BLASTER_TEST_STAGE" = setup ] || [ "$BLASTER_TEST_STAGE" = first-setup ] ||
            { [ "$count" -gt 1 ] && [ "$line" = '(declare-const replayed Int)' ]; }; }; then
        : > "$directory/blocked"
        continue
      fi
      case "$line" in
        '(check-sat)') if [ "$backend" = z3 ]; then echo unsat; fi ;;
        '(exit)') exit 0 ;;
        *) echo success ;;
      esac
    done
    exit 0
    ;;
  tree|orphan-tree|branch)
    if [ "$mode" = branch ]; then next=leaf; else next=branch; fi
    /bin/sh "$0" "$next" "$directory" <&3 &
    child=$!
    printf '%s\n' "$child" > "$directory/$next.pid"
    if [ "$mode" = orphan-tree ]; then exit 0; fi
    wait "$child"
    exit 0
    ;;
  leaf)
    : > "$directory/ready"
    while IFS= read -r line; do :; done
    exit 0
    ;;
  no-read)
    # The descendant waits for a FIFO writer, holding the inherited solver pipes.
    mkfifo "$directory/hold"
    (read -r ignored < "$directory/hold") &
    child=$!
    printf '%s\n' "$child" > "$directory/leaf.pid"
    : > "$directory/ready"
    wait "$child"
    exit 0
    ;;
  flood)
    printf 'USEFUL_STDERR_PREFIX\n' >&2
    dd if=/dev/zero bs=1024 count=256 2>/dev/null | tr '\000' x >&2
    printf '\nUSEFUL_STDERR_SUFFIX\n' >&2
    : > "$directory/flood-complete"
    ;;
  ready)
    printf '%s\n' "$verdict"
    : > "$directory/verdict-ready"
    ;;
esac
: > "$directory/ready"
while IFS= read -r line; do
  printf '%s\n' "$line" >> "$directory/commands"
  case "$line" in
    '(exit)')
      : > "$directory/exit-requested"
      if [ "$mode" = normal-exit ]; then exit 0; fi
      ;;
    '(check-sat)')
      : > "$directory/check-requested"
      case "$mode" in
        silent|ready) ;;
        closed) printf 'CLOSED_STDOUT_DIAGNOSTIC\n' >&2; exec 1>&- ;;
        malformed) printf 'MALFORMED_REPLY_DIAGNOSTIC\n' >&2; printf 'not-a-verdict\n' ;;
        *) printf '%s\n' "$verdict" ;;
      esac
      ;;
    '(get-model)')
      : > "$directory/model-requested"
      case "$mode" in
        silent-model|ready) ;;
        *) printf '()\n' ;;
      esac
      ;;
    '(get-value ('*)
      : > "$directory/model-requested"
      case "$mode" in
        unsupported) printf '((x @opaque))\n' ;;
        *) printf '((x 0))\n' ;;
      esac
      ;;
    *)
      : > "$directory/command-requested"
      case "$mode" in silent) ;; *) printf 'success\n' ;; esac
      ;;
  esac
done
