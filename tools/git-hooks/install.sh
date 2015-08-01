#!/bin/bash

script_dir=$(dirname $0)

if [[ -z "$1" || "$1" = "-h" || "$1" = "--help" ]]; then
    echo "Usage: install.sh /path/to/git/repo" >&2
    exit 1
fi

git_dir="$1/.git"

if [[ ! -d "$git_dir" ]]; then
    echo "$1 is not a git directory." >&2
    exit 1
fi

copy_hook() {
    local from="$script_dir/$1"
    local to="$git_dir/hooks/$2"
    echo "Copying $from to $to" >&2
    cp $from $to
    chmod +x $to
}

copy_hook pre-commit pre-commit
copy_hook post-merge-checkout post-merge
copy_hook post-merge-checkout post-checkout

exit 0


