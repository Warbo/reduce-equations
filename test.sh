#!/usr/bin/env bash

ERR=0
function report {
    if [[ "$1" -eq 0 ]]
    then
        echo "ok - $2"
    else
        echo "not ok - $2"
        ERR=1
    fi
}

cabal build
report "$?" "cabal build"

cabal test --show-details=streaming
report "$?" "cabal test"

for F in test/data/*.json
do
    OUTPUT=$(NIX_EVAL_EXTRA_IMPORTS='[("runtime-arbitrary", "Test.TestInstances")]' \
               cabal run -v0 reduce-equations < "$F")
    report "$?" "Reducing $F"

    echo "$OUTPUT" | jq -e 'type == "array" and (length | . > 0)' > /dev/null
    report "$?" "Got equations from $F"
done

exit "$ERR"
