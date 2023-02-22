// Copyright (c) K Team. All Rights Reserved.

require "domains.md"

module COMMON-SYNTAX
endmodule

module COMMON
imports COMMON-SYNTAX
imports DOMAINS
imports ID

syntax Bool ::= vars(List) [function]

endmodule
