{
  description = "Isla - Symbolic execution engine for Sail ISA specs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" ];
        };
        z3 = pkgs.z3;
        riscv64-gcc = pkgs.pkgsCross.riscv64.stdenv.cc;
        riscv64-binutils = pkgs.pkgsCross.riscv64.binutils;
        riscv64-aliases = pkgs.runCommand "riscv64-linux-gnu-aliases" { } ''
          mkdir -p "$out/bin"
          for tool in ${riscv64-gcc}/bin/riscv64-unknown-linux-gnu-* ${riscv64-binutils}/bin/riscv64-unknown-linux-gnu-*; do
            name="$(basename "$tool")"
            alias="''${name/riscv64-unknown-linux-gnu-/riscv64-linux-gnu-}"
            ln -s "$tool" "$out/bin/$alias"
          done
        '';
      in
      {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            rustToolchain
            rust-analyzer
            cargo-watch
            z3
            riscv64-gcc
            riscv64-binutils
            riscv64-aliases
          ];

          RUST_SRC_PATH = "${rustToolchain}/lib/rustlib/src/rust/library";
          Z3_SYS_Z3_INCLUDE_DIR = "${z3}/include";
          Z3_SYS_Z3_LIB_DIR = "${z3}/lib";
        };
      }
    );
}
