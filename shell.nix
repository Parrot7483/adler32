let
  system = "x86_64-linux";
  pkgs = import <nixpkgs> { inherit system; };
  karamel = builtins.getFlake "github:fstarlang/karamel";
  fstar = karamel.inputs.fstar.packages.${system}.fstar;
  krml = karamel.packages.${system}.default;
in pkgs.mkShell {
  buildInputs = [ 
    fstar 
    krml 
    pkgs.compcert 
  ];
  KRML_HOME = karamel.packages.${system}.karamel.home;
  FSTAR_HOME = fstar.out;
}
