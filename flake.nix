{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";

    nixpkgs-python = {
      url = "github:cachix/nixpkgs-python";
      inputs = { nixpkgs.follows = "nixpkgs"; };
    };
  };

  outputs = { self, nixpkgs, nixpkgs-python, flake-parts, ... } @ inputs: 
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
      ];

      systems = [ "x86_64-linux" "aarch64-darwin" ];

      perSystem = { config, pkgs, system, ... }: with builtins; let
        collect = f: deps: concatMap f (attrValues deps);
        pythonFlake = nixpkgs-python.packages.${system};
        pythonInterp = pythonFlake."3.13.1";
        pip = pkgs.python3Packages;
        # Native libraries that pip-installed wheels (e.g. `kuzu`) need to
        # `dlopen` at import time. `pkgs.stdenv.cc.cc.lib` is the lib-output
        # of gcc that actually contains libstdc++; `.cc` alone does not.
        ld_deps = [
          pkgs.stdenv.cc.cc.lib
        ];
        deps = with pkgs; {
          python = {
            dev = [];
            ci = [
              pythonInterp
              pip.pip
              pip.venvShellHook
            ];
          };

          # General tooling
          tools = {
            dev = [
              bc
              cloc
              curl
              coreutils
              eplot
              gnuplot
              graphviz
              jq
              just
              kuzu
              pandoc
              ripgrep
              timg
              texlivePackages.pdfcrop
              texlivePackages.dvisvgm
              texlivePackages.latexmk
              watch
              yq-go
              texlive.combined.scheme-full
              pdf2svg
              ghostscript
              poppler-utils
            ];
            ci = [];
          };
        };

        ci_deps = collect (v: v.ci) deps;
        dev_deps = (collect (v: v.dev) deps) ++ ci_deps;


      in {
        packages = {
          ci = pkgs.writeShellApplication {
            name = "ci";
            runtimeInputs = deps.ci;
            text = /* bash */ ''
              just ci
            '';
          };
        };

        devShells = {
          default = pkgs.mkShell {
            name = "dev shell";
            venvDir = "./.venv";
            nativeBuildInputs = [ ];
            buildInputs = ci_deps;
            packages = dev_deps;

            shellHook = /* bash */ ''
              SOURCE_DATE_EPOCH=$(date +%s)
              VENV=.venv

              if test ! -d $VENV; then
                python -m venv $VENV
              fi
              source ./$VENV/bin/activate
              export PYTHONPATH=`pwd`/$VENV/${pkgs.python3.sitePackages}/:$PYTHONPATH
              pip install -r requirements.txt

              # Make libstdc++ (and other native deps) discoverable for
              # dlopen-at-import-time wheels like `kuzu`. `mkShell` does
              # not honour a `postShellHook` field, so the export has to
              # live here.
              export LD_LIBRARY_PATH="${pkgs.lib.makeLibraryPath ld_deps}''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

              # Prefer the elan-managed toolchain over whatever lean4 the
              # dev-shell-env transitively brings in. The Nix-packaged elan
              # doesn't drop shims into ~/.elan/bin, so prepending that
              # directory is a no-op. Instead, ask elan which toolchain
              # `lean-toolchain` resolves to and put that bin/ on PATH.
              if command -v elan >/dev/null 2>&1; then
                LEAN_BIN="$(elan which lean 2>/dev/null || true)"
                if [ -n "$LEAN_BIN" ] && [ -x "$LEAN_BIN" ]; then
                  export PATH="$(dirname "$LEAN_BIN"):$PATH"
                fi
              fi
            '';
          };
        };
      };
    };
}

