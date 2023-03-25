with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ mpfr ppl ]
  ++ (with ocamlPackages; [ ocaml findlib dune_3 apron batteries camlidl cmdliner menhir menhirLib zarith yojson])
  ;

  installPhase = ''
    mkdir -p $out/bin
    for p in jasminc jazz2tex jazz2cl
    do
      cp _build/default/$p.exe $out/bin/$p
    done
  '';
}
