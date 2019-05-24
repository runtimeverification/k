#!/usr/bin/env bash

for test_list in assignment lookup inkeys remove; do
    i=1
    while read line; do
        spec_file="$test_list-$i-spec.k"
        module_name="$(echo $test_list | tr '[:lower:]' '[:upper:]')"
        if [[ ! -f "$spec_file" ]] && [[ ! -f "failing/$spec_file" ]]; then
            {   echo "// Copyright (c) 2019 K Team. All Rights Reserved."
                echo ""
                echo "requires \"map-tests.k\""
                echo ""
                echo "module $module_name-$i-SPEC"
                echo "    imports MAP-TESTS"
                echo ""
                echo "    $line"
                echo ""
                echo "endmodule"
            } > $spec_file
            make CHECK='> ' $spec_file
        fi
        i=$((i + 1))
    done < $test_list
done
