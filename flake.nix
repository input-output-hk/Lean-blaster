{
  description = "Lean Blaster — SMT-based tactic for Lean 4";

  inputs = {
    nixpkgs.follows = "lean4-nix/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];

      perSystem = {
        system,
        pkgs,
        ...
      }: let
        leanPkgs = pkgs.lean;
        src = pkgs.lib.cleanSource ./.;
        inherit (pkgs) makeWrapper;
        blaster = leanPkgs.buildLeanPackage {
          name = "Blaster";
          roots = ["Blaster"];
          inherit src;
          leancFlags = ["-O3"];
        };
        z3check = leanPkgs.buildLeanPackage {
          name = "Z3Check";
          roots = ["Z3Check"];
          inherit src;
        };
        z3checkWrapped = pkgs.runCommand "z3check" {nativeBuildInputs = [makeWrapper];} ''
          mkdir -p $out/bin
          cp ${z3check.executable}/bin/* $out/bin/
          wrapProgram $out/bin/z3check --prefix PATH : ${pkgs.lib.makeBinPath [pkgs.z3]}
        '';
        tests = leanPkgs.buildLeanPackage {
          name = "Tests";
          roots = ["Tests"];
          deps = [blaster];
          inherit src;
          overrideBuildModAttrs = _final: prev: {
            buildInputs = (prev.buildInputs or []) ++ [pkgs.z3];
          };
        };
      in {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (lean4-nix.readToolchainFile ./lean-toolchain)
            (_final: prev: {
              z3 = prev.z3.overrideAttrs {
                version = "4.15.2";
                src = prev.fetchFromGitHub {
                  owner = "Z3Prover";
                  repo = "z3";
                  rev = "z3-4.15.2";
                  hash = "sha256-hUGZdr0VPxZ0mEUpcck1AC0MpyZMjiMw/kK8WX7t0xU=";
                };
              };
            })
          ];
        };

        packages = {
          default = blaster.modRoot;
          z3check = z3checkWrapped;
        };

        checks = {
          blaster = blaster.modRoot;
          z3check = z3checkWrapped;
          tests = tests.modRoot;
          smoke-test = pkgs.runCommand "blaster-smoke-test" {
            buildInputs = [leanPkgs.lean-all pkgs.z3];
            LEAN_PATH = "${blaster.modRoot}";
          } ''
            lean ${src}/tests/nix/TestBlaster.lean
            touch $out
          '';
        };

        devShells.default = pkgs.mkShell {
          packages = [leanPkgs.lean-all pkgs.z3 pkgs.elan];
        };
      };
    };
}
