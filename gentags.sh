#!/bin/sh

command -v coqtags >/dev/null 2>&1 || { echo >&2 "You don't have coqtags, so I'm not generating a TAGS file."; exit 0; }
cd js
coqtags *.v
cd -
