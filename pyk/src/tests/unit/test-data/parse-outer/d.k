requires "b.k"
requires "c.k"

module D-SYNTAX
endmodule

module D
    imports D-SYNTAX
    imports B
    imports C
endmodule
