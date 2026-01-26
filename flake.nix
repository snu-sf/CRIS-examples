{
  description = "CRIS development environment";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        coq = pkgs.coq_8_20;
        coqPackages = pkgs.mkCoqPackages coq;
        callPackage = pkgs.lib.callPackageWith (pkgs // params // set);
        params = {
          inherit (coqPackages) mkCoqDerivation lib stdlib;
          inherit (coq) ocamlPackages;
        };
        set = {
          inherit coq;
          paco = callPackage coqPackages.paco.override { version = "4.2.3"; };
          ExtLib = callPackage coqPackages.ExtLib.override { version = "0.12.2"; };
          ITree = callPackage coqPackages.ITree.override { version = "5.2.1"; };
          Ordinal = callPackage coqPackages.Ordinal.override { version = "0.5.4"; };
          stdpp = callPackage coqPackages.stdpp.override { version = "1.12.0"; };
          iris = callPackage coqPackages.iris.override { version = "4.4.0"; };
        };
      in
      {
        devShell = pkgs.mkShell {
          buildInputs = pkgs.lib.attrValues set;
        };
      }
    );
}
