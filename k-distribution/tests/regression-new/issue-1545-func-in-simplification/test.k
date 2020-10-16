// Copyright (c) 2018-2020 K Team. All Rights Reserved.
module TEST
    imports INT
    rule (A *Int I2) +Int (I3 /Int A) => I2 *Int I3 [simplification]
    rule (A +Int I2) +Int (I3 -Int A) => I2 +Int I3
endmodule
