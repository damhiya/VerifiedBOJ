{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    coq
    coqPackages.VST
    compcert
  ];
}
