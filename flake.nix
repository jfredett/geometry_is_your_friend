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
        ld_deps = [
          pkgs.stdenv.cc.cc
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
              pandoc
              ripgrep
              timg
              watch
              yq-go
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
            '';

            postShellHook = /* bash */ ''
              export LD_LIBRARY_PATH="${pkgs.lib.makeLibraryPath ld_deps}"
            '';
          };
        };
      };
    };
}

