module KERNELC-THREADS-SYNTAX imports KERNELC-SYNTAX
  syntax Exp ::= spawn Exp 
               | acquire ( Exp ) [strict] 
               | release ( Exp ) [strict] 
               | join ( Exp ) [strict]
end module
