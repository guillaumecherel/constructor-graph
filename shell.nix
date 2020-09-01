with import <nixpkgs> {};
stdenv.mkDerivation {
    name = "dependency-graph"; 
    buildInputs = [ rustc cargo rustup ];
}
