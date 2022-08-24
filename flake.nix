{
  description = "Lean 4 library heavily focused on category theory and theoretical computer science";

  inputs.lean.url = github:leanprover/lean4-nightly/nightly-2022-08-15;

  outputs = { self, nixpkgs, flake-utils, lean }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      leanPkgs = lean.packages.${system};
      pkg = with pkgs;
        leanPkgs.buildLeanPackage.override (old1: {
          lean-vscode = old1.lean-vscode.override (old2: {
            vscodeExtensions = with vscode-extensions; [ vscodevim.vim ] ++ old2.vscodeExtensions;
          });
        }) {
          name = "Catlib4";
          src = ./.;
        };
    in {
      packages = pkg;
    });
}
