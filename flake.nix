{
  description = "RBGS: refinement-based game semantics, in Rocq";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"
      ];

      eachSystem = f:
        nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      # rocq-rbgs.opam pins rocq-core and rocq-stdlib to 9.2.0, which
      # nixpkgs does not package yet (it is still on 9.1.1), so we bump
      # the sources in place.  Both build from source in a few minutes.
      rocqFor = pkgs:
        pkgs.rocqPackages.overrideScope (final: prev: {
          rocq-core = prev.rocq-core.overrideAttrs (_: {
            version = "9.2.0";
            src = pkgs.fetchFromGitHub {
              owner = "rocq-prover";
              repo = "rocq";
              rev = "V9.2.0";
              hash = "sha256-rVhv2GLImdVPgRwwTQ+wiWNtRUflMrES0ElIrdTIN1s=";
            };

            # nixpkgs builds only rocq-runtime and rocq-core.  Build the
            # coqide-server dune package too: it installs `coqidetop`, the
            # XML-protocol server that RocqIDE and Coqtail drive.  Without
            # it Coqtail reports "could not find coqidetop in <store path>".
            buildPhase = ''
              runHook preBuild
              make dunestrap
              dune build -p rocq-runtime,rocq-core,coqide-server -j $NIX_BUILD_CORES
              runHook postBuild
            '';

            installPhase = ''
              runHook preInstall
              dune install --prefix $out rocq-runtime rocq-core coqide-server
              ln -s $out/lib/rocq-runtime $OCAMLFIND_DESTDIR/rocq-runtime
              ln -s $out/lib/rocq-core $OCAMLFIND_DESTDIR/rocq-core
              runHook postInstall
            '';
          });

          stdlib = prev.stdlib.overrideAttrs (_: {
            version = "9.2.0";
            src = pkgs.fetchFromGitHub {
              owner = "rocq-prover";
              repo = "stdlib";
              rev = "V9.2.0";
              hash = "sha256-ySNY8XUQOH6B1B2p+39jdJ7UjIMrRDl499JJwpLEHuM=";
            };
          });
        });

      # Rocq 9.2 installs only the `rocq` driver, but ./configure,
      # coqrel/configure and the generated Makefile still call the
      # pre-9.0 command names.  Supply them as thin wrappers rather than
      # patching the build scripts.
      legacyNamesFor = pkgs: rocq:
        let
          wrapper = name: sub: pkgs.writeShellScriptBin name ''
            exec ${rocq}/bin/rocq ${sub} "$@"
          '';
        in pkgs.symlinkJoin {
          name = "rocq-legacy-names";
          paths = [
            (wrapper "coqc" "c")
            (wrapper "coqdep" "dep")
            (wrapper "coqdoc" "doc")
            (wrapper "coqtop" "repl")
            (wrapper "coq_makefile" "makefile")
          ];
        };
    in {
      devShells = eachSystem (pkgs:
        let
          rocqPackages = rocqFor pkgs;
          rocq = rocqPackages.rocq-core;
        in {
          default = pkgs.mkShell {
            packages = [
              rocq
              rocqPackages.stdlib
              (legacyNamesFor pkgs rocq)
              pkgs.gnumake
              pkgs.git
            ];

            # Coqtail reads $COQBIN as its search path for coqidetop.
            COQBIN = "${rocq}/bin";

            shellHook = ''
              echo "rbgs: $(rocq c --version | head -1)"
              echo "first time:  ./configure -nocompcert && make -j"
            '';
          };
        });

      # models/IntSpec.v is self-contained: it depends on nothing in the
      # repository and on no package beyond the standard library, so it
      # can be checked on its own without configuring the project.
      packages = eachSystem (pkgs:
        let rocqPackages = rocqFor pkgs; in rec {
          default = intspec;
          intspec = pkgs.stdenv.mkDerivation {
            pname = "rbgs-intspec";
            version = "dev";
            src = ./models;
            nativeBuildInputs = [
              rocqPackages.rocq-core
              rocqPackages.stdlib
            ];
            dontConfigure = true;
            buildPhase = "rocq c -R . models IntSpec.v";
            installPhase = "mkdir -p $out && cp IntSpec.vo $out/";
          };
        });
    };
}
