{
  description = "Lean 4 development environment";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      flake-utils,
      nixpkgs,
    }@inputs:

    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [

            # Toolchain manager, providing the `lean`, `lake` and `leanc` shims.
            # Deliberately not `pkgs.lean4`: a Mathlib project pins its compiler in
            # `lean-toolchain`, and `lake exe cache get` only serves prebuilt oleans
            # for that exact version — so a store-pinned Lean would mean compiling
            # Mathlib from source on every bump. elan resolves the pin instead.
            #
            # On Linux, nixpkgs' elan patches each toolchain it downloads (ELF
            # interpreter, `cc` wrappers for lake/leanc), so no patchelf or
            # LD_LIBRARY_PATH is needed. Those patches embed store paths that are
            # not GC roots; if a toolchain breaks after garbage collection,
            # `elan toolchain uninstall` it and let elan reinstall.
            elan

            # `lake` resolves dependencies over git; the Mathlib cache over https
            git
            curl

          ];

          # Pin the CA bundle used by elan, curl and git downloads instead of
          # relying on the host's /etc/ssl layout.
          shellHook = ''
            export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
          '';
        };

      }
    );

}
