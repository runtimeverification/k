kmod KERNELC-THREADS-SYNTAX is including KERNELC-SYNTAX
  syntax Exp ::= spawn Exp 
               | acquire ( Exp ) [strict] 
               | release ( Exp ) [strict] 
               | join ( Exp ) [strict]
endkm
