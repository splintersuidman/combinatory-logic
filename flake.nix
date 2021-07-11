{
  description = "Explorations in combinatory logic with Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          agdaPackages = pkgs.agdaPackages;

          version = "0";
          everythingFile = "./index.agda";
      in {
        packages.combinatory-logic = agdaPackages.mkDerivation {
          inherit version;
          pname = "combinatory-logic";
          src = ./.;
          buildInputs = [ agdaPackages.standard-library ];
          inherit everythingFile;
        };

        packages.combinatory-logic-doc = agdaPackages.mkDerivation {
          inherit version;
          pname = "combinatory-logic-doc";
          src = ./.;
          buildInputs = [ agdaPackages.standard-library ];

          buildPhase = ''
            runHook preBuild
            agda -i ${dirOf everythingFile} --html ${everythingFile} --html-dir html
            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            mkdir -p $out
            mkdir -p $out/doc
            cp html/* $out/doc
            runHook postInstall
          '';
        };

        defaultPackage = self.packages.${system}.combinatory-logic;
      });
}
