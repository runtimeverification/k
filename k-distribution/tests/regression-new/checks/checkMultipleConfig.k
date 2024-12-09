module CHECKMULTIPLECONFIG
  imports INT
  configuration <extraLocalConfig> 1 </extraLocalConfig>
  configuration <mainConfig> <extraLocalConfig/> </mainConfig>
endmodule
