{
  description = "LF (Software Foundations) dev shell";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "aarch64-darwin";
      pkgs = import nixpkgs { inherit system; };
    in {
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          pkgs.coq
          pkgs.coqPackages.stdlib
        ];
        shellHook = ''
            unset COQPATH
          '';
      };
    };
}
