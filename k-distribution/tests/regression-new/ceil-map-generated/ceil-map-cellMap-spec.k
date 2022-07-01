// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-map.k"

module CEIL-MAP-CELLMAP-SPEC
    imports CEIL-MAP

    claim <k> testCell(_K1, _A1, _B1, _K2, _A2, _B2) => . </k>
          <cellMap> _CELLMAP => ?_ </cellMap>

endmodule
