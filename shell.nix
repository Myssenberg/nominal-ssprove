let
  pkgs = import ./pkgs.nix;
in pkgs.stdenv.mkDerivation {
  name = "ssprove-shell";
  buildInputs = [
    pkgs.glibcLocales
    pkgs.ssprove
    pkgs.coqPackages.coqide
    (pkgs.vim_configurable.customize {
        name = "vim";
        vimrcConfig = {
          packages.myVimPackage.start = with pkgs.vimPlugins; [
            Coqtail
            vim-unicoder
          ];
          customRC = ''
            syntax on
            colorscheme default
            let &t_ut='''
            set relativenumber
            set tabstop=2
            set shiftwidth=2
            set softtabstop=2
            set expandtab
            set backspace=indent,eol,start
            filetype plugin on
            filetype indent on
            hi def CoqtailChecked      ctermbg=7
            hi def CoqtailSent         ctermbg=3
            hi def link CoqtailError   Error
            hi def link CoqtailOmitted coqProofAdmit
          '';
        };
      })
  ];
}
