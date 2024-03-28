{

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
  inputs.nixpkgsCoq = {
    # Nixpkgs containing coq 8.10.2
    url = "github:NixOS/nixpkgs/4c2e7becf1c942553dadd6527996d25dbf5a7136";
    flake = false;
  };

  inputs.nixpkgsHs = {
    # Nixpkgs containing GHC 8.4.3
    url = "github:NixOS/nixpkgs/0bcbb978795bab0f1a45accc211b8b0e349f1cdb";
    flake = false;
  };

  inputs.flake-utils.url =
    "github:numtide/flake-utils/997f7efcb746a9c140ce1f13c72263189225f482";
  inputs.flake-compat.url =
    "https://flakehub.com/f/edolstra/flake-compat/1.tar.gz";
  outputs = { self, nixpkgsCoq, nixpkgsHs, flake-utils, nixpkgs, flake-compat }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        pkgsCoq = import nixpkgsCoq { inherit system; };
        pkgsHs = import nixpkgsHs { inherit system; };
      in rec {
        packages = (import ./default.nix) {
          pkgs = pkgsCoq;
          ghcPackagesCustom = pkgsHs.haskell.packages.ghc843;
        };
        devShells = {
          default = pkgsCoq.mkShell {
            inputsFrom = [ packages.haskellHs2Coq packages.coqHs2Coq ];

            nativeBuildInputs = [
              pkgs.gnumake
              pkgs.stack
              pkgs.cabal-install # some example projects don't have stack.yaml, so we need cabal
              pkgs.xorg.lndir
              pkgs.haskellPackages.hoogle
              pkgs.haskellPackages.haskell-language-server
            ];

            # Set the locale to en_US.UTF-8
            LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
            LANG = "en_US.UTF-8";
            # Required to sync nixpkgs from flake url with nixpkgs in the shell
            shellHook = ''
              export NIX_PATH="nixpkgs=${nixpkgsHs}"
            '';
          };
        };
      });
}
