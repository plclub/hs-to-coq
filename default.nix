# How to use this file:
#
# To work on the Coq code related to hs-to-rocq:
#   nix-shell -A coqPackages.hs-to-rocq
#
# To build the hs-to-rocq utility:
#   nix-build -A haskellPackages.hs-to-rocq
# After building, you can run result/bin/hs-to-rocq

{ coqPackages ? "coqPackages_8_10"
, ghcVersion  ? "ghc884"

, rev    ? "4c2e7becf1c942553dadd6527996d25dbf5a7136"
, sha256 ? "10dzi5xizgm9b3p5k963h5mmp0045nkcsabqyarpr7mj151f6jpm"

, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let
  coqPackages' = pkgs.${coqPackages} // {
    hs-to-rocq = with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
      name = "coq${coq.coq-version}-hs-to-rocq-${version}";
      version = "1.0";

      src =
        if pkgs.lib.inNixShell
        then null
        else if pkgs ? coqFilterSource
             then pkgs.coqFilterSource [] ./.
             else ./.;

      buildInputs = [
        coq coq.ocaml coq.camlp5 coq.findlib mathcomp
      ];
      enableParallelBuilding = true;

      buildPhase = "make -j$NIX_BUILD_CORES";
      preBuild = "coq_makefile -f _CoqProject -o Makefile";
      installPhase = "mkdir -p $out";
      # installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

      env = pkgs.buildEnv { name = name; paths = buildInputs; };
      passthru = {
        compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" "8.10" ];
     };
    };
  };

  haskellPackages' = pkgs.haskell.packages.${ghcVersion} // {
    hs-to-rocq =
      with pkgs.haskell.lib;
      with pkgs.haskell.packages.${ghcVersion}.override {
        overrides = self: super: {
          tasty      = doJailbreak super.tasty;
          indents    = doJailbreak super.indents;
          validation = doJailbreak super.validation;
        };
      };
      callCabal2nix "hs-to-rocq" ./. {};
  };

in {
  coqPackages = coqPackages';
  haskellPackages = haskellPackages';
}
