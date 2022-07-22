with (import <nixpkgs> {});

let
  agda = pkgs.agda.withPackages (p: [ p.standard-library p.cubical ]);
in
  mkShell {
    buildInputs = [ agda ];
  }

