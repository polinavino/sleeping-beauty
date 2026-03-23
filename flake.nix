{
  description = "Sleeping Beauty Agda formalization";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        agdaWithLibs = pkgs.agda.withPackages (p: [ p.standard-library ]);
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = [ agdaWithLibs ];
        };
      }
    );
}
