requires "foundry.md"

module S2KlibZModforgeZSubstdZModsrcZModCommonBase-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModCommonBaseContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModCommonBaseContract ::= "S2KlibZModforgeZSubstdZModsrcZModCommonBase" [symbol("contract_lib%forge-std%src%CommonBase")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModScriptBase-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModScriptBaseContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModScriptBaseContract ::= "S2KlibZModforgeZSubstdZModsrcZModScriptBase" [symbol("contract_lib%forge-std%src%ScriptBase")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModTestBase-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModTestBaseContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestBaseContract ::= "S2KlibZModforgeZSubstdZModsrcZModTestBase" [symbol("contract_lib%forge-std%src%TestBase")]

endmodule

module S2KsrcZModCse-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KsrcZModCseContract
    
    syntax S2KsrcZModCseContract ::= "S2KsrcZModCse" [symbol("contract_src%Cse")]
    
    syntax Bytes ::= S2KsrcZModCseContract "." S2KsrcZModCseMethod [function, symbol("method_src%Cse")]
    
    syntax S2KsrcZModCseMethod ::= "S2Kf" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "bool" ")" [symbol("method_src%Cse_S2Kf_uint256_uint256_bool")]
    
    rule  ( S2KsrcZModCse . S2Kf ( V0_x : uint256 , V1_y : uint256 , V2_z : bool ) => #abiCallData ( "f" , ( #uint256 ( V0_x ) , ( #uint256 ( V1_y ) , ( #bool ( V2_z ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_x )
       andBool ( #rangeUInt ( 256 , V1_y )
       andBool ( #rangeBool ( V2_z )
               )))
      
    
    rule  ( selector ( "f(uint256,uint256,bool)" ) => 2150829809 )
      

endmodule

module S2KtestZModCseTest-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KtestZModCseTestContract
    
    syntax S2KtestZModCseTestContract ::= "S2KtestZModCseTest" [symbol("contract_test%CseTest")]
    
    syntax Bytes ::= S2KtestZModCseTestContract "." S2KtestZModCseTestMethod [function, symbol("method_test%CseTest")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KISZUndTEST" "(" ")" [symbol("method_test%CseTest_S2KISZUndTEST_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KexcludeArtifacts" "(" ")" [symbol("method_test%CseTest_S2KexcludeArtifacts_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KexcludeContracts" "(" ")" [symbol("method_test%CseTest_S2KexcludeContracts_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KexcludeSelectors" "(" ")" [symbol("method_test%CseTest_S2KexcludeSelectors_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KexcludeSenders" "(" ")" [symbol("method_test%CseTest_S2KexcludeSenders_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2Kfailed" "(" ")" [symbol("method_test%CseTest_S2Kfailed_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KsetUp" "(" ")" [symbol("method_test%CseTest_S2KsetUp_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KtargetArtifactSelectors" "(" ")" [symbol("method_test%CseTest_S2KtargetArtifactSelectors_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KtargetArtifacts" "(" ")" [symbol("method_test%CseTest_S2KtargetArtifacts_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KtargetContracts" "(" ")" [symbol("method_test%CseTest_S2KtargetContracts_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KtargetInterfaces" "(" ")" [symbol("method_test%CseTest_S2KtargetInterfaces_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KtargetSelectors" "(" ")" [symbol("method_test%CseTest_S2KtargetSelectors_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KtargetSenders" "(" ")" [symbol("method_test%CseTest_S2KtargetSenders_")]
    
    syntax S2KtestZModCseTestMethod ::= "S2KtestZUndf" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "bool" ")" [symbol("method_test%CseTest_S2KtestZUndf_uint256_uint256_bool")]
    
    rule  ( S2KtestZModCseTest . S2KISZUndTEST ( ) => #abiCallData ( "IS_TEST" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KexcludeArtifacts ( ) => #abiCallData ( "excludeArtifacts" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KexcludeContracts ( ) => #abiCallData ( "excludeContracts" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KexcludeSelectors ( ) => #abiCallData ( "excludeSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KexcludeSenders ( ) => #abiCallData ( "excludeSenders" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2Kfailed ( ) => #abiCallData ( "failed" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KsetUp ( ) => #abiCallData ( "setUp" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KtargetArtifactSelectors ( ) => #abiCallData ( "targetArtifactSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KtargetArtifacts ( ) => #abiCallData ( "targetArtifacts" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KtargetContracts ( ) => #abiCallData ( "targetContracts" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KtargetInterfaces ( ) => #abiCallData ( "targetInterfaces" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KtargetSelectors ( ) => #abiCallData ( "targetSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KtargetSenders ( ) => #abiCallData ( "targetSenders" , .TypedArgs ) )
      
    
    rule  ( S2KtestZModCseTest . S2KtestZUndf ( V0_x : uint256 , V1_y : uint256 , V2_z : bool ) => #abiCallData ( "test_f" , ( #uint256 ( V0_x ) , ( #uint256 ( V1_y ) , ( #bool ( V2_z ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_x )
       andBool ( #rangeUInt ( 256 , V1_y )
       andBool ( #rangeBool ( V2_z )
               )))
      
    
    rule  ( selector ( "IS_TEST()" ) => 4202047188 )
      
    
    rule  ( selector ( "excludeArtifacts()" ) => 3041954473 )
      
    
    rule  ( selector ( "excludeContracts()" ) => 3792478065 )
      
    
    rule  ( selector ( "excludeSelectors()" ) => 2957397980 )
      
    
    rule  ( selector ( "excludeSenders()" ) => 517440284 )
      
    
    rule  ( selector ( "failed()" ) => 3124842406 )
      
    
    rule  ( selector ( "setUp()" ) => 177362148 )
      
    
    rule  ( selector ( "targetArtifactSelectors()" ) => 1725540768 )
      
    
    rule  ( selector ( "targetArtifacts()" ) => 2233625729 )
      
    
    rule  ( selector ( "targetContracts()" ) => 1064470260 )
      
    
    rule  ( selector ( "targetInterfaces()" ) => 719206528 )
      
    
    rule  ( selector ( "targetSelectors()" ) => 2439649222 )
      
    
    rule  ( selector ( "targetSenders()" ) => 1046363171 )
      
    
    rule  ( selector ( "test_f(uint256,uint256,bool)" ) => 3978597910 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165Contract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165Contract ::= "S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165" [symbol("contract_lib%forge-std%src%interfaces%IERC165")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165Contract "." S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165Method [function, symbol("method_lib%forge-std%src%interfaces%IERC165")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165Method ::= "S2KsupportsInterface" "(" Int ":" "bytes4" ")" [symbol("method_lib%forge-std%src%interfaces%IERC165_S2KsupportsInterface_bytes4")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC165 . S2KsupportsInterface ( V0_interfaceID : bytes4 ) => #abiCallData ( "supportsInterface" , ( #bytes4 ( V0_interfaceID ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 4 , V0_interfaceID )
      
    
    rule  ( selector ( "supportsInterface(bytes4)" ) => 33540519 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Contract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Contract ::= "S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20" [symbol("contract_lib%forge-std%src%interfaces%IERC20")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Contract "." S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method [function, symbol("method_lib%forge-std%src%interfaces%IERC20")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2Kallowance" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2Kallowance_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2Kapprove" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2Kapprove_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2KbalanceOf" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2KbalanceOf_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2Kdecimals" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2Kdecimals_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2Kname" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2Kname_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2Ksymbol" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2Ksymbol_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2KtotalSupply" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2KtotalSupply_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2Ktransfer" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2Ktransfer_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20Method ::= "S2KtransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC20_S2KtransferFrom_address_address_uint256")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2Kallowance ( V0_owner : address , V1_spender : address ) => #abiCallData ( "allowance" , ( #address ( V0_owner ) , ( #address ( V1_spender ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_owner )
       andBool ( #rangeAddress ( V1_spender )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2Kapprove ( V0_spender : address , V1_amount : uint256 ) => #abiCallData ( "approve" , ( #address ( V0_spender ) , ( #uint256 ( V1_amount ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_spender )
       andBool ( #rangeUInt ( 256 , V1_amount )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2KbalanceOf ( V0_account : address ) => #abiCallData ( "balanceOf" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2Kdecimals ( ) => #abiCallData ( "decimals" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2Kname ( ) => #abiCallData ( "name" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2Ksymbol ( ) => #abiCallData ( "symbol" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2KtotalSupply ( ) => #abiCallData ( "totalSupply" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2Ktransfer ( V0_to : address , V1_amount : uint256 ) => #abiCallData ( "transfer" , ( #address ( V0_to ) , ( #uint256 ( V1_amount ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_to )
       andBool ( #rangeUInt ( 256 , V1_amount )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC20 . S2KtransferFrom ( V0_from : address , V1_to : address , V2_amount : uint256 ) => #abiCallData ( "transferFrom" , ( #address ( V0_from ) , ( #address ( V1_to ) , ( #uint256 ( V2_amount ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_from )
       andBool ( #rangeAddress ( V1_to )
       andBool ( #rangeUInt ( 256 , V2_amount )
               )))
      
    
    rule  ( selector ( "allowance(address,address)" ) => 3714247998 )
      
    
    rule  ( selector ( "approve(address,uint256)" ) => 157198259 )
      
    
    rule  ( selector ( "balanceOf(address)" ) => 1889567281 )
      
    
    rule  ( selector ( "decimals()" ) => 826074471 )
      
    
    rule  ( selector ( "name()" ) => 117300739 )
      
    
    rule  ( selector ( "symbol()" ) => 2514000705 )
      
    
    rule  ( selector ( "totalSupply()" ) => 404098525 )
      
    
    rule  ( selector ( "transfer(address,uint256)" ) => 2835717307 )
      
    
    rule  ( selector ( "transferFrom(address,address,uint256)" ) => 599290589 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Contract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Contract ::= "S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721" [symbol("contract_lib%forge-std%src%interfaces%IERC721")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Contract "." S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method [function, symbol("method_lib%forge-std%src%interfaces%IERC721")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2Kapprove" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2Kapprove_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KbalanceOf" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KbalanceOf_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KgetApproved" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KgetApproved_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KisApprovedForAll" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KisApprovedForAll_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KownerOf" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KownerOf_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KsafeTransferFrom_address_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KsafeTransferFrom_address_address_uint256_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KsetApprovalForAll" "(" Int ":" "address" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KsetApprovalForAll_address_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KsupportsInterface" "(" Int ":" "bytes4" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KsupportsInterface_bytes4")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Method ::= "S2KtransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721_S2KtransferFrom_address_address_uint256")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2Kapprove ( V0__approved : address , V1__tokenId : uint256 ) => #abiCallData ( "approve" , ( #address ( V0__approved ) , ( #uint256 ( V1__tokenId ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__approved )
       andBool ( #rangeUInt ( 256 , V1__tokenId )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KbalanceOf ( V0__owner : address ) => #abiCallData ( "balanceOf" , ( #address ( V0__owner ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0__owner )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KgetApproved ( V0__tokenId : uint256 ) => #abiCallData ( "getApproved" , ( #uint256 ( V0__tokenId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__tokenId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KisApprovedForAll ( V0__owner : address , V1__operator : address ) => #abiCallData ( "isApprovedForAll" , ( #address ( V0__owner ) , ( #address ( V1__operator ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__owner )
       andBool ( #rangeAddress ( V1__operator )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KownerOf ( V0__tokenId : uint256 ) => #abiCallData ( "ownerOf" , ( #uint256 ( V0__tokenId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__tokenId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KsafeTransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KsafeTransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 , V3_data : bytes ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , ( #bytes ( V3_data ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KsetApprovalForAll ( V0__operator : address , V1__approved : bool ) => #abiCallData ( "setApprovalForAll" , ( #address ( V0__operator ) , ( #bool ( V1__approved ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__operator )
       andBool ( #rangeBool ( V1__approved )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KsupportsInterface ( V0_interfaceID : bytes4 ) => #abiCallData ( "supportsInterface" , ( #bytes4 ( V0_interfaceID ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 4 , V0_interfaceID )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721 . S2KtransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 ) => #abiCallData ( "transferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
               )))
      
    
    rule  ( selector ( "approve(address,uint256)" ) => 157198259 )
      
    
    rule  ( selector ( "balanceOf(address)" ) => 1889567281 )
      
    
    rule  ( selector ( "getApproved(uint256)" ) => 135795452 )
      
    
    rule  ( selector ( "isApprovedForAll(address,address)" ) => 3917867461 )
      
    
    rule  ( selector ( "ownerOf(uint256)" ) => 1666326814 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256)" ) => 1115958798 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256,bytes)" ) => 3096268766 )
      
    
    rule  ( selector ( "setApprovalForAll(address,bool)" ) => 2720838757 )
      
    
    rule  ( selector ( "supportsInterface(bytes4)" ) => 33540519 )
      
    
    rule  ( selector ( "transferFrom(address,address,uint256)" ) => 599290589 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableContract ::= "S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable" [symbol("contract_lib%forge-std%src%interfaces%IERC721Enumerable")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableContract "." S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod [function, symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2Kapprove" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2Kapprove_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KbalanceOf" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KbalanceOf_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KgetApproved" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KgetApproved_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KisApprovedForAll" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KisApprovedForAll_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KownerOf" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KownerOf_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KsafeTransferFrom_address_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KsafeTransferFrom_address_address_uint256_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KsetApprovalForAll" "(" Int ":" "address" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KsetApprovalForAll_address_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KsupportsInterface" "(" Int ":" "bytes4" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KsupportsInterface_bytes4")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KtokenByIndex" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KtokenByIndex_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KtokenOfOwnerByIndex" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KtokenOfOwnerByIndex_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KtotalSupply" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KtotalSupply_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721EnumerableMethod ::= "S2KtransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Enumerable_S2KtransferFrom_address_address_uint256")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2Kapprove ( V0__approved : address , V1__tokenId : uint256 ) => #abiCallData ( "approve" , ( #address ( V0__approved ) , ( #uint256 ( V1__tokenId ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__approved )
       andBool ( #rangeUInt ( 256 , V1__tokenId )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KbalanceOf ( V0__owner : address ) => #abiCallData ( "balanceOf" , ( #address ( V0__owner ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0__owner )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KgetApproved ( V0__tokenId : uint256 ) => #abiCallData ( "getApproved" , ( #uint256 ( V0__tokenId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__tokenId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KisApprovedForAll ( V0__owner : address , V1__operator : address ) => #abiCallData ( "isApprovedForAll" , ( #address ( V0__owner ) , ( #address ( V1__operator ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__owner )
       andBool ( #rangeAddress ( V1__operator )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KownerOf ( V0__tokenId : uint256 ) => #abiCallData ( "ownerOf" , ( #uint256 ( V0__tokenId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__tokenId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KsafeTransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KsafeTransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 , V3_data : bytes ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , ( #bytes ( V3_data ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KsetApprovalForAll ( V0__operator : address , V1__approved : bool ) => #abiCallData ( "setApprovalForAll" , ( #address ( V0__operator ) , ( #bool ( V1__approved ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__operator )
       andBool ( #rangeBool ( V1__approved )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KsupportsInterface ( V0_interfaceID : bytes4 ) => #abiCallData ( "supportsInterface" , ( #bytes4 ( V0_interfaceID ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 4 , V0_interfaceID )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KtokenByIndex ( V0__index : uint256 ) => #abiCallData ( "tokenByIndex" , ( #uint256 ( V0__index ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KtokenOfOwnerByIndex ( V0__owner : address , V1__index : uint256 ) => #abiCallData ( "tokenOfOwnerByIndex" , ( #address ( V0__owner ) , ( #uint256 ( V1__index ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__owner )
       andBool ( #rangeUInt ( 256 , V1__index )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KtotalSupply ( ) => #abiCallData ( "totalSupply" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Enumerable . S2KtransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 ) => #abiCallData ( "transferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
               )))
      
    
    rule  ( selector ( "approve(address,uint256)" ) => 157198259 )
      
    
    rule  ( selector ( "balanceOf(address)" ) => 1889567281 )
      
    
    rule  ( selector ( "getApproved(uint256)" ) => 135795452 )
      
    
    rule  ( selector ( "isApprovedForAll(address,address)" ) => 3917867461 )
      
    
    rule  ( selector ( "ownerOf(uint256)" ) => 1666326814 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256)" ) => 1115958798 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256,bytes)" ) => 3096268766 )
      
    
    rule  ( selector ( "setApprovalForAll(address,bool)" ) => 2720838757 )
      
    
    rule  ( selector ( "supportsInterface(bytes4)" ) => 33540519 )
      
    
    rule  ( selector ( "tokenByIndex(uint256)" ) => 1332530407 )
      
    
    rule  ( selector ( "tokenOfOwnerByIndex(address,uint256)" ) => 796154969 )
      
    
    rule  ( selector ( "totalSupply()" ) => 404098525 )
      
    
    rule  ( selector ( "transferFrom(address,address,uint256)" ) => 599290589 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataContract ::= "S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata" [symbol("contract_lib%forge-std%src%interfaces%IERC721Metadata")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataContract "." S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod [function, symbol("method_lib%forge-std%src%interfaces%IERC721Metadata")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2Kapprove" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2Kapprove_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KbalanceOf" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KbalanceOf_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KgetApproved" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KgetApproved_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KisApprovedForAll" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KisApprovedForAll_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2Kname" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2Kname_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KownerOf" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KownerOf_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KsafeTransferFrom_address_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KsafeTransferFrom_address_address_uint256_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KsetApprovalForAll" "(" Int ":" "address" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KsetApprovalForAll_address_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KsupportsInterface" "(" Int ":" "bytes4" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KsupportsInterface_bytes4")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2Ksymbol" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2Ksymbol_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KtokenURI" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KtokenURI_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721MetadataMethod ::= "S2KtransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721Metadata_S2KtransferFrom_address_address_uint256")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2Kapprove ( V0__approved : address , V1__tokenId : uint256 ) => #abiCallData ( "approve" , ( #address ( V0__approved ) , ( #uint256 ( V1__tokenId ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__approved )
       andBool ( #rangeUInt ( 256 , V1__tokenId )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KbalanceOf ( V0__owner : address ) => #abiCallData ( "balanceOf" , ( #address ( V0__owner ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0__owner )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KgetApproved ( V0__tokenId : uint256 ) => #abiCallData ( "getApproved" , ( #uint256 ( V0__tokenId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__tokenId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KisApprovedForAll ( V0__owner : address , V1__operator : address ) => #abiCallData ( "isApprovedForAll" , ( #address ( V0__owner ) , ( #address ( V1__operator ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__owner )
       andBool ( #rangeAddress ( V1__operator )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2Kname ( ) => #abiCallData ( "name" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KownerOf ( V0__tokenId : uint256 ) => #abiCallData ( "ownerOf" , ( #uint256 ( V0__tokenId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__tokenId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KsafeTransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KsafeTransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 , V3_data : bytes ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , ( #bytes ( V3_data ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KsetApprovalForAll ( V0__operator : address , V1__approved : bool ) => #abiCallData ( "setApprovalForAll" , ( #address ( V0__operator ) , ( #bool ( V1__approved ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0__operator )
       andBool ( #rangeBool ( V1__approved )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KsupportsInterface ( V0_interfaceID : bytes4 ) => #abiCallData ( "supportsInterface" , ( #bytes4 ( V0_interfaceID ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 4 , V0_interfaceID )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2Ksymbol ( ) => #abiCallData ( "symbol" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KtokenURI ( V0__tokenId : uint256 ) => #abiCallData ( "tokenURI" , ( #uint256 ( V0__tokenId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0__tokenId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721Metadata . S2KtransferFrom ( V0__from : address , V1__to : address , V2__tokenId : uint256 ) => #abiCallData ( "transferFrom" , ( #address ( V0__from ) , ( #address ( V1__to ) , ( #uint256 ( V2__tokenId ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0__from )
       andBool ( #rangeAddress ( V1__to )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
               )))
      
    
    rule  ( selector ( "approve(address,uint256)" ) => 157198259 )
      
    
    rule  ( selector ( "balanceOf(address)" ) => 1889567281 )
      
    
    rule  ( selector ( "getApproved(uint256)" ) => 135795452 )
      
    
    rule  ( selector ( "isApprovedForAll(address,address)" ) => 3917867461 )
      
    
    rule  ( selector ( "name()" ) => 117300739 )
      
    
    rule  ( selector ( "ownerOf(uint256)" ) => 1666326814 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256)" ) => 1115958798 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256,bytes)" ) => 3096268766 )
      
    
    rule  ( selector ( "setApprovalForAll(address,bool)" ) => 2720838757 )
      
    
    rule  ( selector ( "supportsInterface(bytes4)" ) => 33540519 )
      
    
    rule  ( selector ( "symbol()" ) => 2514000705 )
      
    
    rule  ( selector ( "tokenURI(uint256)" ) => 3363526365 )
      
    
    rule  ( selector ( "transferFrom(address,address,uint256)" ) => 599290589 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiver-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiverContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiverContract ::= "S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiver" [symbol("contract_lib%forge-std%src%interfaces%IERC721TokenReceiver")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiverContract "." S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiverMethod [function, symbol("method_lib%forge-std%src%interfaces%IERC721TokenReceiver")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiverMethod ::= "S2KonERC721Received" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IERC721TokenReceiver_S2KonERC721Received_address_address_uint256_bytes")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIERC721TokenReceiver . S2KonERC721Received ( V0__operator : address , V1__from : address , V2__tokenId : uint256 , V3__data : bytes ) => #abiCallData ( "onERC721Received" , ( #address ( V0__operator ) , ( #address ( V1__from ) , ( #uint256 ( V2__tokenId ) , ( #bytes ( V3__data ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0__operator )
       andBool ( #rangeAddress ( V1__from )
       andBool ( #rangeUInt ( 256 , V2__tokenId )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3__data ) )
               ))))
      
    
    rule  ( selector ( "onERC721Received(address,address,uint256,bytes)" ) => 353073666 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Contract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Contract ::= "S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3" [symbol("contract_lib%forge-std%src%interfaces%IMulticall3")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Contract "." S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method [function, symbol("method_lib%forge-std%src%interfaces%IMulticall3")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2Kaggregate" "(" Int ":" "address" "," Bytes ":" "bytes" "," Int ":" "address" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2Kaggregate_address_bytes_address_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2Kaggregate3" "(" Int ":" "address" "," Int ":" "bool" "," Bytes ":" "bytes" "," Int ":" "address" "," Int ":" "bool" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2Kaggregate3_address_bool_bytes_address_bool_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2Kaggregate3Value" "(" Int ":" "address" "," Int ":" "bool" "," Int ":" "uint256" "," Bytes ":" "bytes" "," Int ":" "address" "," Int ":" "bool" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2Kaggregate3Value_address_bool_uint256_bytes_address_bool_uint256_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KblockAndAggregate" "(" Int ":" "address" "," Bytes ":" "bytes" "," Int ":" "address" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KblockAndAggregate_address_bytes_address_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetBasefee" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetBasefee_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetBlockHash" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetBlockHash_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetBlockNumber" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetBlockNumber_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetChainId" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetChainId_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetCurrentBlockCoinbase" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetCurrentBlockCoinbase_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetCurrentBlockDifficulty" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetCurrentBlockDifficulty_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetCurrentBlockGasLimit" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetCurrentBlockGasLimit_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetCurrentBlockTimestamp" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetCurrentBlockTimestamp_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetEthBalance" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetEthBalance_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KgetLastBlockHash" "(" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KgetLastBlockHash_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KtryAggregate" "(" Int ":" "bool" "," Int ":" "address" "," Bytes ":" "bytes" "," Int ":" "address" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KtryAggregate_bool_address_bytes_address_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3Method ::= "S2KtryBlockAndAggregate" "(" Int ":" "bool" "," Int ":" "address" "," Bytes ":" "bytes" "," Int ":" "address" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%interfaces%IMulticall3_S2KtryBlockAndAggregate_bool_address_bytes_address_bytes")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2Kaggregate ( V0_target_0 : address , V1_callData_0 : bytes , V0_target_1 : address , V1_callData_1 : bytes ) => #abiCallData ( "aggregate" , ( #array ( #tuple ( ( #address ( V0_target_0 ) , ( #bytes ( V1_callData_0 ) , .TypedArgs ) ) ) , 2 , ( #tuple ( ( #address ( V0_target_0 ) , ( #bytes ( V1_callData_0 ) , .TypedArgs ) ) ) , ( #tuple ( ( #address ( V0_target_1 ) , ( #bytes ( V1_callData_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_target_0 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_callData_0 ) )
       andBool ( #rangeAddress ( V0_target_1 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_callData_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2Kaggregate3 ( V0_target_0 : address , V1_allowFailure_0 : bool , V2_callData_0 : bytes , V0_target_1 : address , V1_allowFailure_1 : bool , V2_callData_1 : bytes ) => #abiCallData ( "aggregate3" , ( #array ( #tuple ( ( #address ( V0_target_0 ) , ( #bool ( V1_allowFailure_0 ) , ( #bytes ( V2_callData_0 ) , .TypedArgs ) ) ) ) , 2 , ( #tuple ( ( #address ( V0_target_0 ) , ( #bool ( V1_allowFailure_0 ) , ( #bytes ( V2_callData_0 ) , .TypedArgs ) ) ) ) , ( #tuple ( ( #address ( V0_target_1 ) , ( #bool ( V1_allowFailure_1 ) , ( #bytes ( V2_callData_1 ) , .TypedArgs ) ) ) ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_target_0 )
       andBool ( #rangeBool ( V1_allowFailure_0 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_callData_0 ) )
       andBool ( #rangeAddress ( V0_target_1 )
       andBool ( #rangeBool ( V1_allowFailure_1 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_callData_1 ) )
               ))))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2Kaggregate3Value ( V0_target_0 : address , V1_allowFailure_0 : bool , V2_value_0 : uint256 , V3_callData_0 : bytes , V0_target_1 : address , V1_allowFailure_1 : bool , V2_value_1 : uint256 , V3_callData_1 : bytes ) => #abiCallData ( "aggregate3Value" , ( #array ( #tuple ( ( #address ( V0_target_0 ) , ( #bool ( V1_allowFailure_0 ) , ( #uint256 ( V2_value_0 ) , ( #bytes ( V3_callData_0 ) , .TypedArgs ) ) ) ) ) , 2 , ( #tuple ( ( #address ( V0_target_0 ) , ( #bool ( V1_allowFailure_0 ) , ( #uint256 ( V2_value_0 ) , ( #bytes ( V3_callData_0 ) , .TypedArgs ) ) ) ) ) , ( #tuple ( ( #address ( V0_target_1 ) , ( #bool ( V1_allowFailure_1 ) , ( #uint256 ( V2_value_1 ) , ( #bytes ( V3_callData_1 ) , .TypedArgs ) ) ) ) ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_target_0 )
       andBool ( #rangeBool ( V1_allowFailure_0 )
       andBool ( #rangeUInt ( 256 , V2_value_0 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_callData_0 ) )
       andBool ( #rangeAddress ( V0_target_1 )
       andBool ( #rangeBool ( V1_allowFailure_1 )
       andBool ( #rangeUInt ( 256 , V2_value_1 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_callData_1 ) )
               ))))))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KblockAndAggregate ( V0_target_0 : address , V1_callData_0 : bytes , V0_target_1 : address , V1_callData_1 : bytes ) => #abiCallData ( "blockAndAggregate" , ( #array ( #tuple ( ( #address ( V0_target_0 ) , ( #bytes ( V1_callData_0 ) , .TypedArgs ) ) ) , 2 , ( #tuple ( ( #address ( V0_target_0 ) , ( #bytes ( V1_callData_0 ) , .TypedArgs ) ) ) , ( #tuple ( ( #address ( V0_target_1 ) , ( #bytes ( V1_callData_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_target_0 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_callData_0 ) )
       andBool ( #rangeAddress ( V0_target_1 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_callData_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetBasefee ( ) => #abiCallData ( "getBasefee" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetBlockHash ( V0_blockNumber : uint256 ) => #abiCallData ( "getBlockHash" , ( #uint256 ( V0_blockNumber ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_blockNumber )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetBlockNumber ( ) => #abiCallData ( "getBlockNumber" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetChainId ( ) => #abiCallData ( "getChainId" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetCurrentBlockCoinbase ( ) => #abiCallData ( "getCurrentBlockCoinbase" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetCurrentBlockDifficulty ( ) => #abiCallData ( "getCurrentBlockDifficulty" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetCurrentBlockGasLimit ( ) => #abiCallData ( "getCurrentBlockGasLimit" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetCurrentBlockTimestamp ( ) => #abiCallData ( "getCurrentBlockTimestamp" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetEthBalance ( V0_addr : address ) => #abiCallData ( "getEthBalance" , ( #address ( V0_addr ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_addr )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KgetLastBlockHash ( ) => #abiCallData ( "getLastBlockHash" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KtryAggregate ( V0_requireSuccess : bool , V1_target_0 : address , V2_callData_0 : bytes , V1_target_1 : address , V2_callData_1 : bytes ) => #abiCallData ( "tryAggregate" , ( #bool ( V0_requireSuccess ) , ( #array ( #tuple ( ( #address ( V1_target_0 ) , ( #bytes ( V2_callData_0 ) , .TypedArgs ) ) ) , 2 , ( #tuple ( ( #address ( V1_target_0 ) , ( #bytes ( V2_callData_0 ) , .TypedArgs ) ) ) , ( #tuple ( ( #address ( V1_target_1 ) , ( #bytes ( V2_callData_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_requireSuccess )
       andBool ( #rangeAddress ( V1_target_0 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_callData_0 ) )
       andBool ( #rangeAddress ( V1_target_1 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_callData_1 ) )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModinterfacesZModIMulticall3 . S2KtryBlockAndAggregate ( V0_requireSuccess : bool , V1_target_0 : address , V2_callData_0 : bytes , V1_target_1 : address , V2_callData_1 : bytes ) => #abiCallData ( "tryBlockAndAggregate" , ( #bool ( V0_requireSuccess ) , ( #array ( #tuple ( ( #address ( V1_target_0 ) , ( #bytes ( V2_callData_0 ) , .TypedArgs ) ) ) , 2 , ( #tuple ( ( #address ( V1_target_0 ) , ( #bytes ( V2_callData_0 ) , .TypedArgs ) ) ) , ( #tuple ( ( #address ( V1_target_1 ) , ( #bytes ( V2_callData_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_requireSuccess )
       andBool ( #rangeAddress ( V1_target_0 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_callData_0 ) )
       andBool ( #rangeAddress ( V1_target_1 )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_callData_1 ) )
               )))))
      
    
    rule  ( selector ( "aggregate((address,bytes)[])" ) => 623753794 )
      
    
    rule  ( selector ( "aggregate3((address,bool,bytes)[])" ) => 2192398027 )
      
    
    rule  ( selector ( "aggregate3Value((address,bool,uint256,bytes)[])" ) => 390982257 )
      
    
    rule  ( selector ( "blockAndAggregate((address,bytes)[])" ) => 3272048553 )
      
    
    rule  ( selector ( "getBasefee()" ) => 1046783638 )
      
    
    rule  ( selector ( "getBlockHash(uint256)" ) => 4001541214 )
      
    
    rule  ( selector ( "getBlockNumber()" ) => 1120645468 )
      
    
    rule  ( selector ( "getChainId()" ) => 872998000 )
      
    
    rule  ( selector ( "getCurrentBlockCoinbase()" ) => 2830128974 )
      
    
    rule  ( selector ( "getCurrentBlockDifficulty()" ) => 1916951965 )
      
    
    rule  ( selector ( "getCurrentBlockGasLimit()" ) => 2262111976 )
      
    
    rule  ( selector ( "getCurrentBlockTimestamp()" ) => 254331261 )
      
    
    rule  ( selector ( "getEthBalance(address)" ) => 1294139852 )
      
    
    rule  ( selector ( "getLastBlockHash()" ) => 669543790 )
      
    
    rule  ( selector ( "tryAggregate(bool,(address,bytes)[])" ) => 3169029079 )
      
    
    rule  ( selector ( "tryBlockAndAggregate(bool,(address,bytes)[])" ) => 966083305 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Contract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Contract ::= "S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20" [symbol("contract_lib%forge-std%src%mocks%MockERC20")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Contract "." S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method [function, symbol("method_lib%forge-std%src%mocks%MockERC20")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2KDOMAINZUndSEPARATOR" "(" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2KDOMAINZUndSEPARATOR_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Kallowance" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Kallowance_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Kapprove" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Kapprove_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2KbalanceOf" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2KbalanceOf_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Kdecimals" "(" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Kdecimals_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Kinitialize" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint8" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Kinitialize_string_string_uint8")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Kname" "(" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Kname_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Knonces" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Knonces_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Kpermit" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint8" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Kpermit_address_address_uint256_uint256_uint8_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Ksymbol" "(" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Ksymbol_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2KtotalSupply" "(" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2KtotalSupply_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2Ktransfer" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2Ktransfer_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20Method ::= "S2KtransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC20_S2KtransferFrom_address_address_uint256")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2KDOMAINZUndSEPARATOR ( ) => #abiCallData ( "DOMAIN_SEPARATOR" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Kallowance ( V0_owner : address , V1_spender : address ) => #abiCallData ( "allowance" , ( #address ( V0_owner ) , ( #address ( V1_spender ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_owner )
       andBool ( #rangeAddress ( V1_spender )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Kapprove ( V0_spender : address , V1_amount : uint256 ) => #abiCallData ( "approve" , ( #address ( V0_spender ) , ( #uint256 ( V1_amount ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_spender )
       andBool ( #rangeUInt ( 256 , V1_amount )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2KbalanceOf ( V0_owner : address ) => #abiCallData ( "balanceOf" , ( #address ( V0_owner ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_owner )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Kdecimals ( ) => #abiCallData ( "decimals" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Kinitialize ( V0_name_ : string , V1_symbol_ : string , V2_decimals_ : uint8 ) => #abiCallData ( "initialize" , ( #string ( V0_name_ ) , ( #string ( V1_symbol_ ) , ( #uint8 ( V2_decimals_ ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 8 , V2_decimals_ )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Kname ( ) => #abiCallData ( "name" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Knonces ( V0_ : address ) => #abiCallData ( "nonces" , ( #address ( V0_ ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Kpermit ( V0_owner : address , V1_spender : address , V2_value : uint256 , V3_deadline : uint256 , V4_v : uint8 , V5_r : bytes32 , V6_s : bytes32 ) => #abiCallData ( "permit" , ( #address ( V0_owner ) , ( #address ( V1_spender ) , ( #uint256 ( V2_value ) , ( #uint256 ( V3_deadline ) , ( #uint8 ( V4_v ) , ( #bytes32 ( V5_r ) , ( #bytes32 ( V6_s ) , .TypedArgs ) ) ) ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_owner )
       andBool ( #rangeAddress ( V1_spender )
       andBool ( #rangeUInt ( 256 , V2_value )
       andBool ( #rangeUInt ( 256 , V3_deadline )
       andBool ( #rangeUInt ( 8 , V4_v )
       andBool ( #rangeBytes ( 32 , V5_r )
       andBool ( #rangeBytes ( 32 , V6_s )
               )))))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Ksymbol ( ) => #abiCallData ( "symbol" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2KtotalSupply ( ) => #abiCallData ( "totalSupply" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2Ktransfer ( V0_to : address , V1_amount : uint256 ) => #abiCallData ( "transfer" , ( #address ( V0_to ) , ( #uint256 ( V1_amount ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_to )
       andBool ( #rangeUInt ( 256 , V1_amount )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC20 . S2KtransferFrom ( V0_from : address , V1_to : address , V2_amount : uint256 ) => #abiCallData ( "transferFrom" , ( #address ( V0_from ) , ( #address ( V1_to ) , ( #uint256 ( V2_amount ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_from )
       andBool ( #rangeAddress ( V1_to )
       andBool ( #rangeUInt ( 256 , V2_amount )
               )))
      
    
    rule  ( selector ( "DOMAIN_SEPARATOR()" ) => 910484757 )
      
    
    rule  ( selector ( "allowance(address,address)" ) => 3714247998 )
      
    
    rule  ( selector ( "approve(address,uint256)" ) => 157198259 )
      
    
    rule  ( selector ( "balanceOf(address)" ) => 1889567281 )
      
    
    rule  ( selector ( "decimals()" ) => 826074471 )
      
    
    rule  ( selector ( "initialize(string,string,uint8)" ) => 371521222 )
      
    
    rule  ( selector ( "name()" ) => 117300739 )
      
    
    rule  ( selector ( "nonces(address)" ) => 2127478272 )
      
    
    rule  ( selector ( "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)" ) => 3573918927 )
      
    
    rule  ( selector ( "symbol()" ) => 2514000705 )
      
    
    rule  ( selector ( "totalSupply()" ) => 404098525 )
      
    
    rule  ( selector ( "transfer(address,uint256)" ) => 2835717307 )
      
    
    rule  ( selector ( "transferFrom(address,address,uint256)" ) => 599290589 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Contract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Contract ::= "S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721" [symbol("contract_lib%forge-std%src%mocks%MockERC721")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Contract "." S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method [function, symbol("method_lib%forge-std%src%mocks%MockERC721")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2Kapprove" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2Kapprove_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KbalanceOf" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KbalanceOf_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KgetApproved" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KgetApproved_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2Kinitialize" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2Kinitialize_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KisApprovedForAll" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KisApprovedForAll_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2Kname" "(" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2Kname_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KownerOf" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KownerOf_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KsafeTransferFrom_address_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KsafeTransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KsafeTransferFrom_address_address_uint256_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KsetApprovalForAll" "(" Int ":" "address" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KsetApprovalForAll_address_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KsupportsInterface" "(" Int ":" "bytes4" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KsupportsInterface_bytes4")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2Ksymbol" "(" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2Ksymbol_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KtokenURI" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KtokenURI_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721Method ::= "S2KtransferFrom" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%mocks%MockERC721_S2KtransferFrom_address_address_uint256")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2Kapprove ( V0_spender : address , V1_id : uint256 ) => #abiCallData ( "approve" , ( #address ( V0_spender ) , ( #uint256 ( V1_id ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_spender )
       andBool ( #rangeUInt ( 256 , V1_id )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KbalanceOf ( V0_owner : address ) => #abiCallData ( "balanceOf" , ( #address ( V0_owner ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_owner )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KgetApproved ( V0_id : uint256 ) => #abiCallData ( "getApproved" , ( #uint256 ( V0_id ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_id )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2Kinitialize ( V0_name_ : string , V1_symbol_ : string ) => #abiCallData ( "initialize" , ( #string ( V0_name_ ) , ( #string ( V1_symbol_ ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KisApprovedForAll ( V0_owner : address , V1_operator : address ) => #abiCallData ( "isApprovedForAll" , ( #address ( V0_owner ) , ( #address ( V1_operator ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_owner )
       andBool ( #rangeAddress ( V1_operator )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2Kname ( ) => #abiCallData ( "name" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KownerOf ( V0_id : uint256 ) => #abiCallData ( "ownerOf" , ( #uint256 ( V0_id ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_id )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KsafeTransferFrom ( V0_from : address , V1_to : address , V2_id : uint256 ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0_from ) , ( #address ( V1_to ) , ( #uint256 ( V2_id ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_from )
       andBool ( #rangeAddress ( V1_to )
       andBool ( #rangeUInt ( 256 , V2_id )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KsafeTransferFrom ( V0_from : address , V1_to : address , V2_id : uint256 , V3_data : bytes ) => #abiCallData ( "safeTransferFrom" , ( #address ( V0_from ) , ( #address ( V1_to ) , ( #uint256 ( V2_id ) , ( #bytes ( V3_data ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_from )
       andBool ( #rangeAddress ( V1_to )
       andBool ( #rangeUInt ( 256 , V2_id )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KsetApprovalForAll ( V0_operator : address , V1_approved : bool ) => #abiCallData ( "setApprovalForAll" , ( #address ( V0_operator ) , ( #bool ( V1_approved ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_operator )
       andBool ( #rangeBool ( V1_approved )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KsupportsInterface ( V0_interfaceId : bytes4 ) => #abiCallData ( "supportsInterface" , ( #bytes4 ( V0_interfaceId ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 4 , V0_interfaceId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2Ksymbol ( ) => #abiCallData ( "symbol" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KtokenURI ( V0_id : uint256 ) => #abiCallData ( "tokenURI" , ( #uint256 ( V0_id ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_id )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModmocksZModMockERC721 . S2KtransferFrom ( V0_from : address , V1_to : address , V2_id : uint256 ) => #abiCallData ( "transferFrom" , ( #address ( V0_from ) , ( #address ( V1_to ) , ( #uint256 ( V2_id ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_from )
       andBool ( #rangeAddress ( V1_to )
       andBool ( #rangeUInt ( 256 , V2_id )
               )))
      
    
    rule  ( selector ( "approve(address,uint256)" ) => 157198259 )
      
    
    rule  ( selector ( "balanceOf(address)" ) => 1889567281 )
      
    
    rule  ( selector ( "getApproved(uint256)" ) => 135795452 )
      
    
    rule  ( selector ( "initialize(string,string)" ) => 1289259894 )
      
    
    rule  ( selector ( "isApprovedForAll(address,address)" ) => 3917867461 )
      
    
    rule  ( selector ( "name()" ) => 117300739 )
      
    
    rule  ( selector ( "ownerOf(uint256)" ) => 1666326814 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256)" ) => 1115958798 )
      
    
    rule  ( selector ( "safeTransferFrom(address,address,uint256,bytes)" ) => 3096268766 )
      
    
    rule  ( selector ( "setApprovalForAll(address,bool)" ) => 2720838757 )
      
    
    rule  ( selector ( "supportsInterface(bytes4)" ) => 33540519 )
      
    
    rule  ( selector ( "symbol()" ) => 2514000705 )
      
    
    rule  ( selector ( "tokenURI(uint256)" ) => 3363526365 )
      
    
    rule  ( selector ( "transferFrom(address,address,uint256)" ) => 599290589 )
      

endmodule

module S2KtestZModAssertTest-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KtestZModAssertTestContract
    
    syntax S2KtestZModAssertTestContract ::= "S2KtestZModAssertTest" [symbol("contract_test%AssertTest")]
    
    syntax Bytes ::= S2KtestZModAssertTestContract "." S2KtestZModAssertTestMethod [function, symbol("method_test%AssertTest")]
    
    syntax S2KtestZModAssertTestMethod ::= "S2KtestZUndassertZUndtrue" "(" ")" [symbol("method_test%AssertTest_S2KtestZUndassertZUndtrue_")]
    
    rule  ( S2KtestZModAssertTest . S2KtestZUndassertZUndtrue ( ) => #abiCallData ( "test_assert_true" , .TypedArgs ) )
      
    
    rule  ( selector ( "test_assert_true()" ) => 906863826 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModStdAssertions-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModStdAssertionsContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdAssertionsContract ::= "S2KlibZModforgeZSubstdZModsrcZModStdAssertions" [symbol("contract_lib%forge-std%src%StdAssertions")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModStdAssertionsContract "." S2KlibZModforgeZSubstdZModsrcZModStdAssertionsMethod [function, symbol("method_lib%forge-std%src%StdAssertions")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdAssertionsMethod ::= "S2Kfailed" "(" ")" [symbol("method_lib%forge-std%src%StdAssertions_S2Kfailed_")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdAssertions . S2Kfailed ( ) => #abiCallData ( "failed" , .TypedArgs ) )
      
    
    rule  ( selector ( "failed()" ) => 3124842406 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModStdChains-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModStdChainsContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdChainsContract ::= "S2KlibZModforgeZSubstdZModsrcZModStdChains" [symbol("contract_lib%forge-std%src%StdChains")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModStdCheats-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModStdCheatsContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdCheatsContract ::= "S2KlibZModforgeZSubstdZModsrcZModStdCheats" [symbol("contract_lib%forge-std%src%StdCheats")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModStdCheatsSafe-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModStdCheatsSafeContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdCheatsSafeContract ::= "S2KlibZModforgeZSubstdZModsrcZModStdCheatsSafe" [symbol("contract_lib%forge-std%src%StdCheatsSafe")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModstdError-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModstdErrorContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorContract ::= "S2KlibZModforgeZSubstdZModsrcZModstdError" [symbol("contract_lib%forge-std%src%stdError")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModstdErrorContract "." S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod [function, symbol("method_lib%forge-std%src%stdError")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KarithmeticError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KarithmeticError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KassertionError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KassertionError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KdivisionError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KdivisionError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KencodeStorageError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KencodeStorageError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KenumConversionError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KenumConversionError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KindexOOBError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KindexOOBError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KmemOverflowError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KmemOverflowError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KpopError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KpopError_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdErrorMethod ::= "S2KzeroVarError" "(" ")" [symbol("method_lib%forge-std%src%stdError_S2KzeroVarError_")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KarithmeticError ( ) => #abiCallData ( "arithmeticError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KassertionError ( ) => #abiCallData ( "assertionError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KdivisionError ( ) => #abiCallData ( "divisionError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KencodeStorageError ( ) => #abiCallData ( "encodeStorageError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KenumConversionError ( ) => #abiCallData ( "enumConversionError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KindexOOBError ( ) => #abiCallData ( "indexOOBError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KmemOverflowError ( ) => #abiCallData ( "memOverflowError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KpopError ( ) => #abiCallData ( "popError" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModstdError . S2KzeroVarError ( ) => #abiCallData ( "zeroVarError" , .TypedArgs ) )
      
    
    rule  ( selector ( "arithmeticError()" ) => 2308253967 )
      
    
    rule  ( selector ( "assertionError()" ) => 271788407 )
      
    
    rule  ( selector ( "divisionError()" ) => 4202187332 )
      
    
    rule  ( selector ( "encodeStorageError()" ) => 3512788190 )
      
    
    rule  ( selector ( "enumConversionError()" ) => 501503328 )
      
    
    rule  ( selector ( "indexOOBError()" ) => 99517970 )
      
    
    rule  ( selector ( "memOverflowError()" ) => 2557239144 )
      
    
    rule  ( selector ( "popError()" ) => 2989344077 )
      
    
    rule  ( selector ( "zeroVarError()" ) => 3061221850 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModStdInvariant-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModStdInvariantContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantContract ::= "S2KlibZModforgeZSubstdZModsrcZModStdInvariant" [symbol("contract_lib%forge-std%src%StdInvariant")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModStdInvariantContract "." S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod [function, symbol("method_lib%forge-std%src%StdInvariant")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KexcludeArtifacts" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KexcludeArtifacts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KexcludeContracts" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KexcludeContracts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KexcludeSelectors" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KexcludeSelectors_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KexcludeSenders" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KexcludeSenders_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KtargetArtifactSelectors" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KtargetArtifactSelectors_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KtargetArtifacts" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KtargetArtifacts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KtargetContracts" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KtargetContracts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KtargetInterfaces" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KtargetInterfaces_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KtargetSelectors" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KtargetSelectors_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdInvariantMethod ::= "S2KtargetSenders" "(" ")" [symbol("method_lib%forge-std%src%StdInvariant_S2KtargetSenders_")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KexcludeArtifacts ( ) => #abiCallData ( "excludeArtifacts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KexcludeContracts ( ) => #abiCallData ( "excludeContracts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KexcludeSelectors ( ) => #abiCallData ( "excludeSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KexcludeSenders ( ) => #abiCallData ( "excludeSenders" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KtargetArtifactSelectors ( ) => #abiCallData ( "targetArtifactSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KtargetArtifacts ( ) => #abiCallData ( "targetArtifacts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KtargetContracts ( ) => #abiCallData ( "targetContracts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KtargetInterfaces ( ) => #abiCallData ( "targetInterfaces" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KtargetSelectors ( ) => #abiCallData ( "targetSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModStdInvariant . S2KtargetSenders ( ) => #abiCallData ( "targetSenders" , .TypedArgs ) )
      
    
    rule  ( selector ( "excludeArtifacts()" ) => 3041954473 )
      
    
    rule  ( selector ( "excludeContracts()" ) => 3792478065 )
      
    
    rule  ( selector ( "excludeSelectors()" ) => 2957397980 )
      
    
    rule  ( selector ( "excludeSenders()" ) => 517440284 )
      
    
    rule  ( selector ( "targetArtifactSelectors()" ) => 1725540768 )
      
    
    rule  ( selector ( "targetArtifacts()" ) => 2233625729 )
      
    
    rule  ( selector ( "targetContracts()" ) => 1064470260 )
      
    
    rule  ( selector ( "targetInterfaces()" ) => 719206528 )
      
    
    rule  ( selector ( "targetSelectors()" ) => 2439649222 )
      
    
    rule  ( selector ( "targetSenders()" ) => 1046363171 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModstdJson-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModstdJsonContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdJsonContract ::= "S2KlibZModforgeZSubstdZModsrcZModstdJson" [symbol("contract_lib%forge-std%src%stdJson")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModstdMath-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModstdMathContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdMathContract ::= "S2KlibZModforgeZSubstdZModsrcZModstdMath" [symbol("contract_lib%forge-std%src%stdMath")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModstdStorage-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModstdStorageContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdStorageContract ::= "S2KlibZModforgeZSubstdZModsrcZModstdStorage" [symbol("contract_lib%forge-std%src%stdStorage")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModstdStorageSafe-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModstdStorageSafeContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdStorageSafeContract ::= "S2KlibZModforgeZSubstdZModsrcZModstdStorageSafe" [symbol("contract_lib%forge-std%src%stdStorageSafe")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModStdStyle-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModStdStyleContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdStyleContract ::= "S2KlibZModforgeZSubstdZModsrcZModStdStyle" [symbol("contract_lib%forge-std%src%StdStyle")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModstdToml-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModstdTomlContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModstdTomlContract ::= "S2KlibZModforgeZSubstdZModsrcZModstdToml" [symbol("contract_lib%forge-std%src%stdToml")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModStdUtils-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModStdUtilsContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModStdUtilsContract ::= "S2KlibZModforgeZSubstdZModsrcZModStdUtils" [symbol("contract_lib%forge-std%src%StdUtils")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModTest-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModTestContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestContract ::= "S2KlibZModforgeZSubstdZModsrcZModTest" [symbol("contract_lib%forge-std%src%Test")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModTestContract "." S2KlibZModforgeZSubstdZModsrcZModTestMethod [function, symbol("method_lib%forge-std%src%Test")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KISZUndTEST" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KISZUndTEST_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KexcludeArtifacts" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KexcludeArtifacts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KexcludeContracts" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KexcludeContracts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KexcludeSelectors" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KexcludeSelectors_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KexcludeSenders" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KexcludeSenders_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2Kfailed" "(" ")" [symbol("method_lib%forge-std%src%Test_S2Kfailed_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KtargetArtifactSelectors" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KtargetArtifactSelectors_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KtargetArtifacts" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KtargetArtifacts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KtargetContracts" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KtargetContracts_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KtargetInterfaces" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KtargetInterfaces_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KtargetSelectors" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KtargetSelectors_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModTestMethod ::= "S2KtargetSenders" "(" ")" [symbol("method_lib%forge-std%src%Test_S2KtargetSenders_")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KISZUndTEST ( ) => #abiCallData ( "IS_TEST" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KexcludeArtifacts ( ) => #abiCallData ( "excludeArtifacts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KexcludeContracts ( ) => #abiCallData ( "excludeContracts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KexcludeSelectors ( ) => #abiCallData ( "excludeSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KexcludeSenders ( ) => #abiCallData ( "excludeSenders" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2Kfailed ( ) => #abiCallData ( "failed" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KtargetArtifactSelectors ( ) => #abiCallData ( "targetArtifactSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KtargetArtifacts ( ) => #abiCallData ( "targetArtifacts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KtargetContracts ( ) => #abiCallData ( "targetContracts" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KtargetInterfaces ( ) => #abiCallData ( "targetInterfaces" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KtargetSelectors ( ) => #abiCallData ( "targetSelectors" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModTest . S2KtargetSenders ( ) => #abiCallData ( "targetSenders" , .TypedArgs ) )
      
    
    rule  ( selector ( "IS_TEST()" ) => 4202047188 )
      
    
    rule  ( selector ( "excludeArtifacts()" ) => 3041954473 )
      
    
    rule  ( selector ( "excludeContracts()" ) => 3792478065 )
      
    
    rule  ( selector ( "excludeSelectors()" ) => 2957397980 )
      
    
    rule  ( selector ( "excludeSenders()" ) => 517440284 )
      
    
    rule  ( selector ( "failed()" ) => 3124842406 )
      
    
    rule  ( selector ( "targetArtifactSelectors()" ) => 1725540768 )
      
    
    rule  ( selector ( "targetArtifacts()" ) => 2233625729 )
      
    
    rule  ( selector ( "targetContracts()" ) => 1064470260 )
      
    
    rule  ( selector ( "targetInterfaces()" ) => 719206528 )
      
    
    rule  ( selector ( "targetSelectors()" ) => 2439649222 )
      
    
    rule  ( selector ( "targetSenders()" ) => 1046363171 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModVm-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModVmContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmContract ::= "S2KlibZModforgeZSubstdZModsrcZModVm" [symbol("contract_lib%forge-std%src%Vm")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModVmContract "." S2KlibZModforgeZSubstdZModsrcZModVmMethod [function, symbol("method_lib%forge-std%src%Vm")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kaccesses" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2Kaccesses_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KactiveFork" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KactiveFork_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kaddr" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kaddr_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KallowCheatcodes" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KallowCheatcodes_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbs_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbs_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbs_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbs_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbsDecimal_int256_int256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbsDecimal_int256_int256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbsDecimal_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqAbsDecimal_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRel" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRel_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRel" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRel_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRel" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRel_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRel" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRel_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRelDecimal_int256_int256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRelDecimal_int256_int256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRelDecimal_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertApproxEqRelDecimal_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_address_address_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_address_address_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bool_bool_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bool_bool_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes32_bytes32_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes32_bytes32_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes_bytes_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_bytes_bytes_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_int256_int256_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_int256_int256_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_string_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEq_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEqDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEqDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEqDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertEqDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertFalse" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertFalse_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertFalse" "(" Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertFalse_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGe" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGe_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGe" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGe_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGe" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGe_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGe" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGe_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGeDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGeDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGeDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGeDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGt" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGt_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGt" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGt_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGt" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGt_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGt" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGt_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGtDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGtDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGtDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertGtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertGtDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLe" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLe_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLe" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLe_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLe" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLe_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLe" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLe_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLeDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLeDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLeDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLeDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLt" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLt_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLt" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLt_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLt" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLt_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLt" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLt_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLtDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLtDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLtDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertLtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertLtDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_address_address_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_address_address_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bool_bool_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bool_bool_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes32_bytes32_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes32_bytes32_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes_bytes_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_bytes_bytes_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_int256_int256_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_int256_int256_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_string_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEq_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEqDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEqDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEqDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertNotEqDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertTrue" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertTrue_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KassertTrue" "(" Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KassertTrue_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kassume" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2Kassume_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KblobBaseFee" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KblobBaseFee_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kblobhashes" "(" Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Kblobhashes_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kbreakpoint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Kbreakpoint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kbreakpoint" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2Kbreakpoint_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kbroadcast" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2Kbroadcast_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kbroadcast" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2Kbroadcast_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kbroadcast" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kbroadcast_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KbroadcastRawTransaction" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KbroadcastRawTransaction_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KchainId" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KchainId_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KclearMockedCalls" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KclearMockedCalls_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcloseFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KcloseFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kcoinbase" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2Kcoinbase_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcomputeCreate2Address" "(" Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KcomputeCreate2Address_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcomputeCreate2Address" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KcomputeCreate2Address_bytes32_bytes32_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcomputeCreateAddress" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KcomputeCreateAddress_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcopyFile" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KcopyFile_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateDir" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateDir_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateFork" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateFork_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateFork" "(" String ":" "string" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateFork_string_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateFork" "(" String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateFork_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateSelectFork" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateSelectFork_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateSelectFork" "(" String ":" "string" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateSelectFork_string_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateSelectFork" "(" String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateSelectFork_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateWallet" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateWallet_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateWallet" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateWallet_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KcreateWallet" "(" Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KcreateWallet_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kdeal" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kdeal_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KdeleteSnapshot" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KdeleteSnapshot_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KdeleteSnapshots" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KdeleteSnapshots_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KdeployCode" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KdeployCode_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KdeployCode" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KdeployCode_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KderiveKey" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint32" ")" [symbol("method_lib%forge-std%src%Vm_S2KderiveKey_string_string_uint32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KderiveKey" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KderiveKey_string_string_uint32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KderiveKey" "(" String ":" "string" "," Int ":" "uint32" ")" [symbol("method_lib%forge-std%src%Vm_S2KderiveKey_string_uint32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KderiveKey" "(" String ":" "string" "," Int ":" "uint32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KderiveKey_string_uint32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kdifficulty" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kdifficulty_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KdumpState" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KdumpState_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KensNamehash" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KensNamehash_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvAddress" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvAddress_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvAddress" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvAddress_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvBool" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvBool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvBool" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvBool_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvBytes" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvBytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvBytes" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvBytes_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvBytes32" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvBytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvBytes32" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvBytes32_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvExists" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvExists_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvInt" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvInt_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvInt" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvInt_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_string_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvOr_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvString" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvString_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvString" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvString_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KenvUint" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KenvUint_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ketch" "(" Int ":" "address" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2Ketch_address_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KethZUndgetLogs" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "address" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KethZUndgetLogs_uint256_uint256_address_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kexists" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Kexists_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCall" "(" Int ":" "address" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCall_address_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCall" "(" Int ":" "address" "," Bytes ":" "bytes" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCall_address_bytes_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCall" "(" Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCall_address_uint256_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCall" "(" Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCall_address_uint256_bytes_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCall" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint64" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCall_address_uint256_uint64_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCall" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint64" "," Bytes ":" "bytes" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCall_address_uint256_uint64_bytes_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCallMinGas" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint64" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCallMinGas_address_uint256_uint64_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectCallMinGas" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint64" "," Bytes ":" "bytes" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectCallMinGas_address_uint256_uint64_bytes_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmit" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmit_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmit" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmit_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmit" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmit_bool_bool_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmit" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmit_bool_bool_bool_bool_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmitAnonymous" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmitAnonymous_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmitAnonymous" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmitAnonymous_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmitAnonymous" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmitAnonymous_bool_bool_bool_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectEmitAnonymous" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectEmitAnonymous_bool_bool_bool_bool_bool_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectRevert" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectRevert_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectRevert" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectRevert_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectRevert" "(" Int ":" "bytes4" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectRevert_bytes4")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectSafeMemory" "(" Int ":" "uint64" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectSafeMemory_uint64_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KexpectSafeMemoryCall" "(" Int ":" "uint64" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KexpectSafeMemoryCall_uint64_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kfee" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kfee_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kffi" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Kffi_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KfsMetadata" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KfsMetadata_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetBlobBaseFee" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetBlobBaseFee_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetBlobhashes" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetBlobhashes_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetBlockNumber" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetBlockNumber_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetBlockTimestamp" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetBlockTimestamp_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetCode" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetCode_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetDeployedCode" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetDeployedCode_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetFoundryVersion" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetFoundryVersion_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetLabel" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetLabel_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetMappingKeyAndParentOf" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetMappingKeyAndParentOf_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetMappingLength" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetMappingLength_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetMappingSlotAt" "(" Int ":" "address" "," Int ":" "bytes32" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetMappingSlotAt_address_bytes32_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetNonce" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetNonce_address_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetNonce" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetNonce_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KgetRecordedLogs" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KgetRecordedLogs_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KindexOf" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KindexOf_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KisContext" "(" Int ":" "uint8" ")" [symbol("method_lib%forge-std%src%Vm_S2KisContext_uint8")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KisDir" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KisDir_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KisFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KisFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KisPersistent" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KisPersistent_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KkeyExists" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KkeyExists_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KkeyExistsJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KkeyExistsJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KkeyExistsToml" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KkeyExistsToml_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Klabel" "(" Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Klabel_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KlastCallGas" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KlastCallGas_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kload" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Kload_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KloadAllocs" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KloadAllocs_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmakePersistent" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KmakePersistent_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmakePersistent" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KmakePersistent_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmakePersistent" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KmakePersistent_address_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmakePersistent" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KmakePersistent_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmockCall" "(" Int ":" "address" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KmockCall_address_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmockCall" "(" Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KmockCall_address_uint256_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmockCallRevert" "(" Int ":" "address" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KmockCallRevert_address_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KmockCallRevert" "(" Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KmockCallRevert_address_uint256_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseAddress" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseAddress_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseBool" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseBool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseBytes" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseBytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseBytes32" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseBytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseInt" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseInt_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJson" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJson_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonAddress" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonAddress_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonAddressArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonAddressArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonBool" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonBool_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonBoolArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonBoolArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonBytes" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonBytes_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonBytes32" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonBytes32_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonBytes32Array" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonBytes32Array_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonBytesArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonBytesArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonInt" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonInt_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonIntArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonIntArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonKeys" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonKeys_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonString" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonString_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonStringArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonStringArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonType" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonType_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonType" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonType_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonTypeArray" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonTypeArray_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonUint" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonUint_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseJsonUintArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseJsonUintArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseToml" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseToml_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseToml" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseToml_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlAddress" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlAddress_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlAddressArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlAddressArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlBool" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlBool_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlBoolArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlBoolArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlBytes" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlBytes_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlBytes32" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlBytes32_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlBytes32Array" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlBytes32Array_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlBytesArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlBytesArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlInt" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlInt_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlIntArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlIntArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlKeys" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlKeys_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlString" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlString_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlStringArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlStringArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlUint" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlUint_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseTomlUintArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseTomlUintArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KparseUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KparseUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KpauseGasMetering" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KpauseGasMetering_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kprank" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2Kprank_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kprank" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2Kprank_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kprevrandao" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Kprevrandao_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kprevrandao" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kprevrandao_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KprojectRoot" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KprojectRoot_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kprompt" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Kprompt_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KpromptAddress" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KpromptAddress_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KpromptSecret" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KpromptSecret_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KpromptSecretUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KpromptSecretUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KpromptUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KpromptUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrandomAddress" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KrandomAddress_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrandomUint" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KrandomUint_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrandomUint" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KrandomUint_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadCallers" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadCallers_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadDir" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadDir_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadDir" "(" String ":" "string" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadDir_string_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadDir" "(" String ":" "string" "," Int ":" "uint64" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadDir_string_uint64_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadFileBinary" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadFileBinary_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadLine" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadLine_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KreadLink" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KreadLink_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Krecord" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2Krecord_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrecordLogs" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KrecordLogs_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrememberKey" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KrememberKey_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KremoveDir" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KremoveDir_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KremoveFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KremoveFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kreplace" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Kreplace_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KresetNonce" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KresetNonce_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KresumeGasMetering" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KresumeGasMetering_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrevertTo" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KrevertTo_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrevertToAndDelete" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KrevertToAndDelete_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrevokePersistent" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KrevokePersistent_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrevokePersistent" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KrevokePersistent_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kroll" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kroll_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrollFork" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KrollFork_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrollFork" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KrollFork_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrollFork" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KrollFork_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrollFork" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KrollFork_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Krpc" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Krpc_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Krpc" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Krpc_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrpcUrl" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KrpcUrl_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrpcUrlStructs" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KrpcUrlStructs_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KrpcUrls" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KrpcUrls_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KselectFork" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KselectFork_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeAddress" "(" String ":" "string" "," String ":" "string" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeAddress_string_string_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeAddress" "(" String ":" "string" "," String ":" "string" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeAddress_string_string_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeBool" "(" String ":" "string" "," String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeBool_string_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeBool" "(" String ":" "string" "," String ":" "string" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeBool_string_string_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeBytes" "(" String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeBytes_string_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeBytes" "(" String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeBytes_string_string_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeBytes32" "(" String ":" "string" "," String ":" "string" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeBytes32_string_string_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeBytes32" "(" String ":" "string" "," String ":" "string" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeBytes32_string_string_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeInt" "(" String ":" "string" "," String ":" "string" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeInt_string_string_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeInt" "(" String ":" "string" "," String ":" "string" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeInt_string_string_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeJsonType" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeJsonType_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeJsonType" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeJsonType_string_string_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeString" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeString_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeString" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeString_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeUint" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeUint_string_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeUint" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeUint_string_string_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KserializeUintToHex" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KserializeUintToHex_string_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsetBlockhash" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KsetBlockhash_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsetEnv" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KsetEnv_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsetNonce" "(" Int ":" "address" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KsetNonce_address_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsetNonceUnsafe" "(" Int ":" "address" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%Vm_S2KsetNonceUnsafe_address_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ksign" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Ksign_address_uint256_uint256_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ksign" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Ksign_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ksign" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Ksign_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ksign" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Ksign_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsignCompact" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KsignCompact_address_uint256_uint256_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsignCompact" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KsignCompact_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsignCompact" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KsignCompact_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsignCompact" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KsignCompact_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KsignP256" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KsignP256_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kskip" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2Kskip_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ksleep" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Ksleep_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ksnapshot" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2Ksnapshot_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ksplit" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Ksplit_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstartBroadcast" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstartBroadcast_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstartBroadcast" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KstartBroadcast_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstartBroadcast" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KstartBroadcast_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstartMappingRecording" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstartMappingRecording_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstartPrank" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KstartPrank_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstartPrank" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KstartPrank_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstartStateDiffRecording" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstartStateDiffRecording_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstopAndReturnStateDiff" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstopAndReturnStateDiff_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstopBroadcast" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstopBroadcast_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstopExpectSafeMemory" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstopExpectSafeMemory_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstopMappingRecording" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstopMappingRecording_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KstopPrank" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KstopPrank_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kstore" "(" Int ":" "address" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Kstore_address_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoBase64" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoBase64_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoBase64" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoBase64_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoBase64URL" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoBase64URL_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoBase64URL" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoBase64URL_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoLowercase" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoLowercase_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoString" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoString_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoString" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoString_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoString" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoString_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoString" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoString_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoString" "(" Int ":" "int256" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoString_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoString" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoString_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtoUppercase" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KtoUppercase_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ktransact" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Ktransact_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ktransact" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%Vm_S2Ktransact_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Ktrim" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2Ktrim_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtryFfi" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KtryFfi_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KtxGasPrice" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2KtxGasPrice_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KunixTime" "(" ")" [symbol("method_lib%forge-std%src%Vm_S2KunixTime_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2Kwarp" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%Vm_S2Kwarp_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KwriteFile" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KwriteFile_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KwriteFileBinary" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%Vm_S2KwriteFileBinary_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KwriteJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KwriteJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KwriteJson" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KwriteJson_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KwriteLine" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KwriteLine_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KwriteToml" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KwriteToml_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmMethod ::= "S2KwriteToml" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%Vm_S2KwriteToml_string_string_string")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kaccesses ( V0_target : address ) => #abiCallData ( "accesses" , ( #address ( V0_target ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_target )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KactiveFork ( ) => #abiCallData ( "activeFork" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kaddr ( V0_privateKey : uint256 ) => #abiCallData ( "addr" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KallowCheatcodes ( V0_account : address ) => #abiCallData ( "allowCheatcodes" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbs ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 ) => #abiCallData ( "assertApproxEqAbs" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbs ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqAbs" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbs ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 ) => #abiCallData ( "assertApproxEqAbs" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbs ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqAbs" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbsDecimal ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbsDecimal ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbsDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqAbsDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRel ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 ) => #abiCallData ( "assertApproxEqRel" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRel ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqRel" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRel ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 ) => #abiCallData ( "assertApproxEqRel" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRel ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqRel" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRelDecimal ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRelDecimal ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRelDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertApproxEqRelDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : address , V1_right : address ) => #abiCallData ( "assertEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : address , V1_right : address , V2_error : string ) => #abiCallData ( "assertEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address ) => #abiCallData ( "assertEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : bool , V1_right : bool ) => #abiCallData ( "assertEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : bool , V1_right : bool , V2_error : string ) => #abiCallData ( "assertEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool ) => #abiCallData ( "assertEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : bytes , V1_right : bytes ) => #abiCallData ( "assertEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : bytes , V1_right : bytes , V2_error : string ) => #abiCallData ( "assertEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : bytes32 , V1_right : bytes32 ) => #abiCallData ( "assertEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : bytes32 , V1_right : bytes32 , V2_error : string ) => #abiCallData ( "assertEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 ) => #abiCallData ( "assertEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes ) => #abiCallData ( "assertEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 ) => #abiCallData ( "assertEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : string , V1_right : string ) => #abiCallData ( "assertEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : string , V1_right : string , V2_error : string ) => #abiCallData ( "assertEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string ) => #abiCallData ( "assertEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 ) => #abiCallData ( "assertEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertFalse ( V0_condition : bool ) => #abiCallData ( "assertFalse" , ( #bool ( V0_condition ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertFalse ( V0_condition : bool , V1_error : string ) => #abiCallData ( "assertFalse" , ( #bool ( V0_condition ) , ( #string ( V1_error ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGe ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertGe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGe ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertGe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGe ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertGe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGe ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertGe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertGeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertGeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGt ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertGt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGt ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertGt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGt ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertGt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGt ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertGt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertGtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertGtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertGtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLe ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertLe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLe ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertLe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLe ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertLe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLe ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertLe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertLeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertLeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLt ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertLt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLt ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertLt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLt ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertLt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLt ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertLt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertLtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertLtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertLtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : address , V1_right : address ) => #abiCallData ( "assertNotEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : address , V1_right : address , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address ) => #abiCallData ( "assertNotEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : bool , V1_right : bool ) => #abiCallData ( "assertNotEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : bool , V1_right : bool , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool ) => #abiCallData ( "assertNotEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : bytes , V1_right : bytes ) => #abiCallData ( "assertNotEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : bytes , V1_right : bytes , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : bytes32 , V1_right : bytes32 ) => #abiCallData ( "assertNotEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : bytes32 , V1_right : bytes32 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertNotEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 ) => #abiCallData ( "assertNotEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : string , V1_right : string ) => #abiCallData ( "assertNotEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : string , V1_right : string , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string ) => #abiCallData ( "assertNotEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertNotEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 ) => #abiCallData ( "assertNotEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertNotEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertNotEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertNotEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertNotEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertNotEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertTrue ( V0_condition : bool ) => #abiCallData ( "assertTrue" , ( #bool ( V0_condition ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KassertTrue ( V0_condition : bool , V1_error : string ) => #abiCallData ( "assertTrue" , ( #bool ( V0_condition ) , ( #string ( V1_error ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kassume ( V0_condition : bool ) => #abiCallData ( "assume" , ( #bool ( V0_condition ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KblobBaseFee ( V0_newBlobBaseFee : uint256 ) => #abiCallData ( "blobBaseFee" , ( #uint256 ( V0_newBlobBaseFee ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newBlobBaseFee )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kblobhashes ( V0_hashes_0 : bytes32 , V0_hashes_1 : bytes32 ) => #abiCallData ( "blobhashes" , ( #array ( #bytes32 ( V0_hashes_0 ) , 2 , ( #bytes32 ( V0_hashes_0 ) , ( #bytes32 ( V0_hashes_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeBytes ( 32 , V0_hashes_0 )
       andBool ( #rangeBytes ( 32 , V0_hashes_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kbreakpoint ( V0_char : string ) => #abiCallData ( "breakpoint" , ( #string ( V0_char ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kbreakpoint ( V0_char : string , V1_value : bool ) => #abiCallData ( "breakpoint" , ( #string ( V0_char ) , ( #bool ( V1_value ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kbroadcast ( ) => #abiCallData ( "broadcast" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kbroadcast ( V0_signer : address ) => #abiCallData ( "broadcast" , ( #address ( V0_signer ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_signer )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kbroadcast ( V0_privateKey : uint256 ) => #abiCallData ( "broadcast" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KbroadcastRawTransaction ( V0_data : bytes ) => #abiCallData ( "broadcastRawTransaction" , ( #bytes ( V0_data ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KchainId ( V0_newChainId : uint256 ) => #abiCallData ( "chainId" , ( #uint256 ( V0_newChainId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newChainId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KclearMockedCalls ( ) => #abiCallData ( "clearMockedCalls" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcloseFile ( V0_path : string ) => #abiCallData ( "closeFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kcoinbase ( V0_newCoinbase : address ) => #abiCallData ( "coinbase" , ( #address ( V0_newCoinbase ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_newCoinbase )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcomputeCreate2Address ( V0_salt : bytes32 , V1_initCodeHash : bytes32 ) => #abiCallData ( "computeCreate2Address" , ( #bytes32 ( V0_salt ) , ( #bytes32 ( V1_initCodeHash ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_salt )
       andBool ( #rangeBytes ( 32 , V1_initCodeHash )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcomputeCreate2Address ( V0_salt : bytes32 , V1_initCodeHash : bytes32 , V2_deployer : address ) => #abiCallData ( "computeCreate2Address" , ( #bytes32 ( V0_salt ) , ( #bytes32 ( V1_initCodeHash ) , ( #address ( V2_deployer ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_salt )
       andBool ( #rangeBytes ( 32 , V1_initCodeHash )
       andBool ( #rangeAddress ( V2_deployer )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcomputeCreateAddress ( V0_deployer : address , V1_nonce : uint256 ) => #abiCallData ( "computeCreateAddress" , ( #address ( V0_deployer ) , ( #uint256 ( V1_nonce ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_deployer )
       andBool ( #rangeUInt ( 256 , V1_nonce )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcopyFile ( V0_from : string , V1_to : string ) => #abiCallData ( "copyFile" , ( #string ( V0_from ) , ( #string ( V1_to ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateDir ( V0_path : string , V1_recursive : bool ) => #abiCallData ( "createDir" , ( #string ( V0_path ) , ( #bool ( V1_recursive ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_recursive )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateFork ( V0_urlOrAlias : string ) => #abiCallData ( "createFork" , ( #string ( V0_urlOrAlias ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateFork ( V0_urlOrAlias : string , V1_txHash : bytes32 ) => #abiCallData ( "createFork" , ( #string ( V0_urlOrAlias ) , ( #bytes32 ( V1_txHash ) , .TypedArgs ) ) ) )
       ensures #rangeBytes ( 32 , V1_txHash )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateFork ( V0_urlOrAlias : string , V1_blockNumber : uint256 ) => #abiCallData ( "createFork" , ( #string ( V0_urlOrAlias ) , ( #uint256 ( V1_blockNumber ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 256 , V1_blockNumber )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateSelectFork ( V0_urlOrAlias : string ) => #abiCallData ( "createSelectFork" , ( #string ( V0_urlOrAlias ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateSelectFork ( V0_urlOrAlias : string , V1_txHash : bytes32 ) => #abiCallData ( "createSelectFork" , ( #string ( V0_urlOrAlias ) , ( #bytes32 ( V1_txHash ) , .TypedArgs ) ) ) )
       ensures #rangeBytes ( 32 , V1_txHash )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateSelectFork ( V0_urlOrAlias : string , V1_blockNumber : uint256 ) => #abiCallData ( "createSelectFork" , ( #string ( V0_urlOrAlias ) , ( #uint256 ( V1_blockNumber ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 256 , V1_blockNumber )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateWallet ( V0_walletLabel : string ) => #abiCallData ( "createWallet" , ( #string ( V0_walletLabel ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateWallet ( V0_privateKey : uint256 ) => #abiCallData ( "createWallet" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KcreateWallet ( V0_privateKey : uint256 , V1_walletLabel : string ) => #abiCallData ( "createWallet" , ( #uint256 ( V0_privateKey ) , ( #string ( V1_walletLabel ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kdeal ( V0_account : address , V1_newBalance : uint256 ) => #abiCallData ( "deal" , ( #address ( V0_account ) , ( #uint256 ( V1_newBalance ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_account )
       andBool ( #rangeUInt ( 256 , V1_newBalance )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KdeleteSnapshot ( V0_snapshotId : uint256 ) => #abiCallData ( "deleteSnapshot" , ( #uint256 ( V0_snapshotId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_snapshotId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KdeleteSnapshots ( ) => #abiCallData ( "deleteSnapshots" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KdeployCode ( V0_artifactPath : string ) => #abiCallData ( "deployCode" , ( #string ( V0_artifactPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KdeployCode ( V0_artifactPath : string , V1_constructorArgs : bytes ) => #abiCallData ( "deployCode" , ( #string ( V0_artifactPath ) , ( #bytes ( V1_constructorArgs ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_constructorArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KderiveKey ( V0_mnemonic : string , V1_derivationPath : string , V2_index : uint32 ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #string ( V1_derivationPath ) , ( #uint32 ( V2_index ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 32 , V2_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KderiveKey ( V0_mnemonic : string , V1_derivationPath : string , V2_index : uint32 , V3_language : string ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #string ( V1_derivationPath ) , ( #uint32 ( V2_index ) , ( #string ( V3_language ) , .TypedArgs ) ) ) ) ) )
       ensures #rangeUInt ( 32 , V2_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KderiveKey ( V0_mnemonic : string , V1_index : uint32 ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #uint32 ( V1_index ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 32 , V1_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KderiveKey ( V0_mnemonic : string , V1_index : uint32 , V2_language : string ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #uint32 ( V1_index ) , ( #string ( V2_language ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 32 , V1_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kdifficulty ( V0_newDifficulty : uint256 ) => #abiCallData ( "difficulty" , ( #uint256 ( V0_newDifficulty ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newDifficulty )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KdumpState ( V0_pathToStateJson : string ) => #abiCallData ( "dumpState" , ( #string ( V0_pathToStateJson ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KensNamehash ( V0_name : string ) => #abiCallData ( "ensNamehash" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvAddress ( V0_name : string ) => #abiCallData ( "envAddress" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvAddress ( V0_name : string , V1_delim : string ) => #abiCallData ( "envAddress" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvBool ( V0_name : string ) => #abiCallData ( "envBool" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvBool ( V0_name : string , V1_delim : string ) => #abiCallData ( "envBool" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvBytes ( V0_name : string ) => #abiCallData ( "envBytes" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvBytes ( V0_name : string , V1_delim : string ) => #abiCallData ( "envBytes" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvBytes32 ( V0_name : string ) => #abiCallData ( "envBytes32" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvBytes32 ( V0_name : string , V1_delim : string ) => #abiCallData ( "envBytes32" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvExists ( V0_name : string ) => #abiCallData ( "envExists" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvInt ( V0_name : string ) => #abiCallData ( "envInt" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvInt ( V0_name : string , V1_delim : string ) => #abiCallData ( "envInt" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_defaultValue : address ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #address ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeAddress ( V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_defaultValue : bool ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #bool ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_defaultValue : bytes ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #bytes ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_defaultValue ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_defaultValue : bytes32 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #bytes32 ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeBytes ( 32 , V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_defaultValue : int256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #int256 ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeSInt ( 256 , V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_defaultValue : string ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_defaultValue ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : address , V2_defaultValue_1 : address ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #address ( V2_defaultValue_0 ) , 2 , ( #address ( V2_defaultValue_0 ) , ( #address ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V2_defaultValue_0 )
       andBool ( #rangeAddress ( V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : bool , V2_defaultValue_1 : bool ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #bool ( V2_defaultValue_0 ) , 2 , ( #bool ( V2_defaultValue_0 ) , ( #bool ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V2_defaultValue_0 )
       andBool ( #rangeBool ( V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : bytes32 , V2_defaultValue_1 : bytes32 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #bytes32 ( V2_defaultValue_0 ) , 2 , ( #bytes32 ( V2_defaultValue_0 ) , ( #bytes32 ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V2_defaultValue_0 )
       andBool ( #rangeBytes ( 32 , V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : bytes , V2_defaultValue_1 : bytes ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #bytes ( V2_defaultValue_0 ) , 2 , ( #bytes ( V2_defaultValue_0 ) , ( #bytes ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V2_defaultValue_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_defaultValue_1 ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : int256 , V2_defaultValue_1 : int256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #int256 ( V2_defaultValue_0 ) , 2 , ( #int256 ( V2_defaultValue_0 ) , ( #int256 ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V2_defaultValue_0 )
       andBool ( #rangeSInt ( 256 , V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : string , V2_defaultValue_1 : string ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #string ( V2_defaultValue_0 ) , 2 , ( #string ( V2_defaultValue_0 ) , ( #string ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : uint256 , V2_defaultValue_1 : uint256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #uint256 ( V2_defaultValue_0 ) , 2 , ( #uint256 ( V2_defaultValue_0 ) , ( #uint256 ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V2_defaultValue_0 )
       andBool ( #rangeUInt ( 256 , V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvOr ( V0_name : string , V1_defaultValue : uint256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #uint256 ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 256 , V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvString ( V0_name : string ) => #abiCallData ( "envString" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvString ( V0_name : string , V1_delim : string ) => #abiCallData ( "envString" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvUint ( V0_name : string ) => #abiCallData ( "envUint" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KenvUint ( V0_name : string , V1_delim : string ) => #abiCallData ( "envUint" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ketch ( V0_target : address , V1_newRuntimeBytecode : bytes ) => #abiCallData ( "etch" , ( #address ( V0_target ) , ( #bytes ( V1_newRuntimeBytecode ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_newRuntimeBytecode ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KethZUndgetLogs ( V0_fromBlock : uint256 , V1_toBlock : uint256 , V2_target : address , V3_topics_0 : bytes32 , V3_topics_1 : bytes32 ) => #abiCallData ( "eth_getLogs" , ( #uint256 ( V0_fromBlock ) , ( #uint256 ( V1_toBlock ) , ( #address ( V2_target ) , ( #array ( #bytes32 ( V3_topics_0 ) , 2 , ( #bytes32 ( V3_topics_0 ) , ( #bytes32 ( V3_topics_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_fromBlock )
       andBool ( #rangeUInt ( 256 , V1_toBlock )
       andBool ( #rangeAddress ( V2_target )
       andBool ( #rangeBytes ( 32 , V3_topics_0 )
       andBool ( #rangeBytes ( 32 , V3_topics_1 )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kexists ( V0_path : string ) => #abiCallData ( "exists" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCall ( V0_callee : address , V1_data : bytes ) => #abiCallData ( "expectCall" , ( #address ( V0_callee ) , ( #bytes ( V1_data ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_data ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCall ( V0_callee : address , V1_data : bytes , V2_count : uint64 ) => #abiCallData ( "expectCall" , ( #address ( V0_callee ) , ( #bytes ( V1_data ) , ( #uint64 ( V2_count ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_data ) )
       andBool ( #rangeUInt ( 64 , V2_count )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCall ( V0_callee : address , V1_msgValue : uint256 , V2_data : bytes ) => #abiCallData ( "expectCall" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #bytes ( V2_data ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_data ) )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCall ( V0_callee : address , V1_msgValue : uint256 , V2_data : bytes , V3_count : uint64 ) => #abiCallData ( "expectCall" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #bytes ( V2_data ) , ( #uint64 ( V3_count ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_data ) )
       andBool ( #rangeUInt ( 64 , V3_count )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCall ( V0_callee : address , V1_msgValue : uint256 , V2_gas : uint64 , V3_data : bytes ) => #abiCallData ( "expectCall" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #uint64 ( V2_gas ) , ( #bytes ( V3_data ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , V2_gas )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCall ( V0_callee : address , V1_msgValue : uint256 , V2_gas : uint64 , V3_data : bytes , V4_count : uint64 ) => #abiCallData ( "expectCall" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #uint64 ( V2_gas ) , ( #bytes ( V3_data ) , ( #uint64 ( V4_count ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , V2_gas )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
       andBool ( #rangeUInt ( 64 , V4_count )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCallMinGas ( V0_callee : address , V1_msgValue : uint256 , V2_minGas : uint64 , V3_data : bytes ) => #abiCallData ( "expectCallMinGas" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #uint64 ( V2_minGas ) , ( #bytes ( V3_data ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , V2_minGas )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectCallMinGas ( V0_callee : address , V1_msgValue : uint256 , V2_minGas : uint64 , V3_data : bytes , V4_count : uint64 ) => #abiCallData ( "expectCallMinGas" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #uint64 ( V2_minGas ) , ( #bytes ( V3_data ) , ( #uint64 ( V4_count ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , V2_minGas )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_data ) )
       andBool ( #rangeUInt ( 64 , V4_count )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmit ( ) => #abiCallData ( "expectEmit" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmit ( V0_emitter : address ) => #abiCallData ( "expectEmit" , ( #address ( V0_emitter ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_emitter )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmit ( V0_checkTopic1 : bool , V1_checkTopic2 : bool , V2_checkTopic3 : bool , V3_checkData : bool ) => #abiCallData ( "expectEmit" , ( #bool ( V0_checkTopic1 ) , ( #bool ( V1_checkTopic2 ) , ( #bool ( V2_checkTopic3 ) , ( #bool ( V3_checkData ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeBool ( V0_checkTopic1 )
       andBool ( #rangeBool ( V1_checkTopic2 )
       andBool ( #rangeBool ( V2_checkTopic3 )
       andBool ( #rangeBool ( V3_checkData )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmit ( V0_checkTopic1 : bool , V1_checkTopic2 : bool , V2_checkTopic3 : bool , V3_checkData : bool , V4_emitter : address ) => #abiCallData ( "expectEmit" , ( #bool ( V0_checkTopic1 ) , ( #bool ( V1_checkTopic2 ) , ( #bool ( V2_checkTopic3 ) , ( #bool ( V3_checkData ) , ( #address ( V4_emitter ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeBool ( V0_checkTopic1 )
       andBool ( #rangeBool ( V1_checkTopic2 )
       andBool ( #rangeBool ( V2_checkTopic3 )
       andBool ( #rangeBool ( V3_checkData )
       andBool ( #rangeAddress ( V4_emitter )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmitAnonymous ( ) => #abiCallData ( "expectEmitAnonymous" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmitAnonymous ( V0_emitter : address ) => #abiCallData ( "expectEmitAnonymous" , ( #address ( V0_emitter ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_emitter )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmitAnonymous ( V0_checkTopic0 : bool , V1_checkTopic1 : bool , V2_checkTopic2 : bool , V3_checkTopic3 : bool , V4_checkData : bool ) => #abiCallData ( "expectEmitAnonymous" , ( #bool ( V0_checkTopic0 ) , ( #bool ( V1_checkTopic1 ) , ( #bool ( V2_checkTopic2 ) , ( #bool ( V3_checkTopic3 ) , ( #bool ( V4_checkData ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeBool ( V0_checkTopic0 )
       andBool ( #rangeBool ( V1_checkTopic1 )
       andBool ( #rangeBool ( V2_checkTopic2 )
       andBool ( #rangeBool ( V3_checkTopic3 )
       andBool ( #rangeBool ( V4_checkData )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectEmitAnonymous ( V0_checkTopic0 : bool , V1_checkTopic1 : bool , V2_checkTopic2 : bool , V3_checkTopic3 : bool , V4_checkData : bool , V5_emitter : address ) => #abiCallData ( "expectEmitAnonymous" , ( #bool ( V0_checkTopic0 ) , ( #bool ( V1_checkTopic1 ) , ( #bool ( V2_checkTopic2 ) , ( #bool ( V3_checkTopic3 ) , ( #bool ( V4_checkData ) , ( #address ( V5_emitter ) , .TypedArgs ) ) ) ) ) ) ) )
       ensures ( #rangeBool ( V0_checkTopic0 )
       andBool ( #rangeBool ( V1_checkTopic1 )
       andBool ( #rangeBool ( V2_checkTopic2 )
       andBool ( #rangeBool ( V3_checkTopic3 )
       andBool ( #rangeBool ( V4_checkData )
       andBool ( #rangeAddress ( V5_emitter )
               ))))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectRevert ( ) => #abiCallData ( "expectRevert" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectRevert ( V0_revertData : bytes ) => #abiCallData ( "expectRevert" , ( #bytes ( V0_revertData ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_revertData ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectRevert ( V0_revertData : bytes4 ) => #abiCallData ( "expectRevert" , ( #bytes4 ( V0_revertData ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 4 , V0_revertData )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectSafeMemory ( V0_min : uint64 , V1_max : uint64 ) => #abiCallData ( "expectSafeMemory" , ( #uint64 ( V0_min ) , ( #uint64 ( V1_max ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , V0_min )
       andBool ( #rangeUInt ( 64 , V1_max )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KexpectSafeMemoryCall ( V0_min : uint64 , V1_max : uint64 ) => #abiCallData ( "expectSafeMemoryCall" , ( #uint64 ( V0_min ) , ( #uint64 ( V1_max ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , V0_min )
       andBool ( #rangeUInt ( 64 , V1_max )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kfee ( V0_newBasefee : uint256 ) => #abiCallData ( "fee" , ( #uint256 ( V0_newBasefee ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newBasefee )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kffi ( V0_commandInput_0 : string , V0_commandInput_1 : string ) => #abiCallData ( "ffi" , ( #array ( #string ( V0_commandInput_0 ) , 2 , ( #string ( V0_commandInput_0 ) , ( #string ( V0_commandInput_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KfsMetadata ( V0_path : string ) => #abiCallData ( "fsMetadata" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetBlobBaseFee ( ) => #abiCallData ( "getBlobBaseFee" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetBlobhashes ( ) => #abiCallData ( "getBlobhashes" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetBlockNumber ( ) => #abiCallData ( "getBlockNumber" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetBlockTimestamp ( ) => #abiCallData ( "getBlockTimestamp" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetCode ( V0_artifactPath : string ) => #abiCallData ( "getCode" , ( #string ( V0_artifactPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetDeployedCode ( V0_artifactPath : string ) => #abiCallData ( "getDeployedCode" , ( #string ( V0_artifactPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetFoundryVersion ( ) => #abiCallData ( "getFoundryVersion" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetLabel ( V0_account : address ) => #abiCallData ( "getLabel" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetMappingKeyAndParentOf ( V0_target : address , V1_elementSlot : bytes32 ) => #abiCallData ( "getMappingKeyAndParentOf" , ( #address ( V0_target ) , ( #bytes32 ( V1_elementSlot ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_elementSlot )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetMappingLength ( V0_target : address , V1_mappingSlot : bytes32 ) => #abiCallData ( "getMappingLength" , ( #address ( V0_target ) , ( #bytes32 ( V1_mappingSlot ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_mappingSlot )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetMappingSlotAt ( V0_target : address , V1_mappingSlot : bytes32 , V2_idx : uint256 ) => #abiCallData ( "getMappingSlotAt" , ( #address ( V0_target ) , ( #bytes32 ( V1_mappingSlot ) , ( #uint256 ( V2_idx ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_mappingSlot )
       andBool ( #rangeUInt ( 256 , V2_idx )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetNonce ( V0_addr : address , V1_publicKeyX : uint256 , V2_publicKeyY : uint256 , V3_privateKey : uint256 ) => #abiCallData ( "getNonce" , ( #tuple ( ( #address ( V0_addr ) , ( #uint256 ( V1_publicKeyX ) , ( #uint256 ( V2_publicKeyY ) , ( #uint256 ( V3_privateKey ) , .TypedArgs ) ) ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_addr )
       andBool ( #rangeUInt ( 256 , V1_publicKeyX )
       andBool ( #rangeUInt ( 256 , V2_publicKeyY )
       andBool ( #rangeUInt ( 256 , V3_privateKey )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetNonce ( V0_account : address ) => #abiCallData ( "getNonce" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KgetRecordedLogs ( ) => #abiCallData ( "getRecordedLogs" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KindexOf ( V0_input : string , V1_key : string ) => #abiCallData ( "indexOf" , ( #string ( V0_input ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KisContext ( V0_context : uint8 ) => #abiCallData ( "isContext" , ( #uint8 ( V0_context ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 8 , V0_context )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KisDir ( V0_path : string ) => #abiCallData ( "isDir" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KisFile ( V0_path : string ) => #abiCallData ( "isFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KisPersistent ( V0_account : address ) => #abiCallData ( "isPersistent" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KkeyExists ( V0_json : string , V1_key : string ) => #abiCallData ( "keyExists" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KkeyExistsJson ( V0_json : string , V1_key : string ) => #abiCallData ( "keyExistsJson" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KkeyExistsToml ( V0_toml : string , V1_key : string ) => #abiCallData ( "keyExistsToml" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Klabel ( V0_account : address , V1_newLabel : string ) => #abiCallData ( "label" , ( #address ( V0_account ) , ( #string ( V1_newLabel ) , .TypedArgs ) ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KlastCallGas ( ) => #abiCallData ( "lastCallGas" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kload ( V0_target : address , V1_slot : bytes32 ) => #abiCallData ( "load" , ( #address ( V0_target ) , ( #bytes32 ( V1_slot ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_slot )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KloadAllocs ( V0_pathToAllocsJson : string ) => #abiCallData ( "loadAllocs" , ( #string ( V0_pathToAllocsJson ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmakePersistent ( V0_account : address ) => #abiCallData ( "makePersistent" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmakePersistent ( V0_account0 : address , V1_account1 : address ) => #abiCallData ( "makePersistent" , ( #address ( V0_account0 ) , ( #address ( V1_account1 ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_account0 )
       andBool ( #rangeAddress ( V1_account1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmakePersistent ( V0_account0 : address , V1_account1 : address , V2_account2 : address ) => #abiCallData ( "makePersistent" , ( #address ( V0_account0 ) , ( #address ( V1_account1 ) , ( #address ( V2_account2 ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_account0 )
       andBool ( #rangeAddress ( V1_account1 )
       andBool ( #rangeAddress ( V2_account2 )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmakePersistent ( V0_accounts_0 : address , V0_accounts_1 : address ) => #abiCallData ( "makePersistent" , ( #array ( #address ( V0_accounts_0 ) , 2 , ( #address ( V0_accounts_0 ) , ( #address ( V0_accounts_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_accounts_0 )
       andBool ( #rangeAddress ( V0_accounts_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmockCall ( V0_callee : address , V1_data : bytes , V2_returnData : bytes ) => #abiCallData ( "mockCall" , ( #address ( V0_callee ) , ( #bytes ( V1_data ) , ( #bytes ( V2_returnData ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_data ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_returnData ) )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmockCall ( V0_callee : address , V1_msgValue : uint256 , V2_data : bytes , V3_returnData : bytes ) => #abiCallData ( "mockCall" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #bytes ( V2_data ) , ( #bytes ( V3_returnData ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_data ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_returnData ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmockCallRevert ( V0_callee : address , V1_data : bytes , V2_revertData : bytes ) => #abiCallData ( "mockCallRevert" , ( #address ( V0_callee ) , ( #bytes ( V1_data ) , ( #bytes ( V2_revertData ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_data ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_revertData ) )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KmockCallRevert ( V0_callee : address , V1_msgValue : uint256 , V2_data : bytes , V3_revertData : bytes ) => #abiCallData ( "mockCallRevert" , ( #address ( V0_callee ) , ( #uint256 ( V1_msgValue ) , ( #bytes ( V2_data ) , ( #bytes ( V3_revertData ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeAddress ( V0_callee )
       andBool ( #rangeUInt ( 256 , V1_msgValue )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_data ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V3_revertData ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseAddress ( V0_stringifiedValue : string ) => #abiCallData ( "parseAddress" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseBool ( V0_stringifiedValue : string ) => #abiCallData ( "parseBool" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseBytes ( V0_stringifiedValue : string ) => #abiCallData ( "parseBytes" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseBytes32 ( V0_stringifiedValue : string ) => #abiCallData ( "parseBytes32" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseInt ( V0_stringifiedValue : string ) => #abiCallData ( "parseInt" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJson ( V0_json : string ) => #abiCallData ( "parseJson" , ( #string ( V0_json ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJson ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJson" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonAddress ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonAddress" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonAddressArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonAddressArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonBool ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBool" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonBoolArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBoolArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonBytes ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytes" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonBytes32 ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytes32" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonBytes32Array ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytes32Array" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonBytesArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytesArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonInt ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonInt" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonIntArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonIntArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonKeys ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonKeys" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonString ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonString" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonStringArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonStringArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonType ( V0_json : string , V1_typeDescription : string ) => #abiCallData ( "parseJsonType" , ( #string ( V0_json ) , ( #string ( V1_typeDescription ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonType ( V0_json : string , V1_key : string , V2_typeDescription : string ) => #abiCallData ( "parseJsonType" , ( #string ( V0_json ) , ( #string ( V1_key ) , ( #string ( V2_typeDescription ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonTypeArray ( V0_json : string , V1_key : string , V2_typeDescription : string ) => #abiCallData ( "parseJsonTypeArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , ( #string ( V2_typeDescription ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonUint ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonUint" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseJsonUintArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonUintArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseToml ( V0_toml : string ) => #abiCallData ( "parseToml" , ( #string ( V0_toml ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseToml ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseToml" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlAddress ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlAddress" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlAddressArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlAddressArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlBool ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBool" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlBoolArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBoolArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlBytes ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytes" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlBytes32 ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytes32" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlBytes32Array ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytes32Array" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlBytesArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytesArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlInt ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlInt" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlIntArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlIntArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlKeys ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlKeys" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlString ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlString" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlStringArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlStringArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlUint ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlUint" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseTomlUintArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlUintArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KparseUint ( V0_stringifiedValue : string ) => #abiCallData ( "parseUint" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KpauseGasMetering ( ) => #abiCallData ( "pauseGasMetering" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kprank ( V0_msgSender : address ) => #abiCallData ( "prank" , ( #address ( V0_msgSender ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_msgSender )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kprank ( V0_msgSender : address , V1_txOrigin : address ) => #abiCallData ( "prank" , ( #address ( V0_msgSender ) , ( #address ( V1_txOrigin ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_msgSender )
       andBool ( #rangeAddress ( V1_txOrigin )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kprevrandao ( V0_newPrevrandao : bytes32 ) => #abiCallData ( "prevrandao" , ( #bytes32 ( V0_newPrevrandao ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_newPrevrandao )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kprevrandao ( V0_newPrevrandao : uint256 ) => #abiCallData ( "prevrandao" , ( #uint256 ( V0_newPrevrandao ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newPrevrandao )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KprojectRoot ( ) => #abiCallData ( "projectRoot" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kprompt ( V0_promptText : string ) => #abiCallData ( "prompt" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KpromptAddress ( V0_promptText : string ) => #abiCallData ( "promptAddress" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KpromptSecret ( V0_promptText : string ) => #abiCallData ( "promptSecret" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KpromptSecretUint ( V0_promptText : string ) => #abiCallData ( "promptSecretUint" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KpromptUint ( V0_promptText : string ) => #abiCallData ( "promptUint" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrandomAddress ( ) => #abiCallData ( "randomAddress" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrandomUint ( ) => #abiCallData ( "randomUint" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrandomUint ( V0_min : uint256 , V1_max : uint256 ) => #abiCallData ( "randomUint" , ( #uint256 ( V0_min ) , ( #uint256 ( V1_max ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_min )
       andBool ( #rangeUInt ( 256 , V1_max )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadCallers ( ) => #abiCallData ( "readCallers" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadDir ( V0_path : string ) => #abiCallData ( "readDir" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadDir ( V0_path : string , V1_maxDepth : uint64 ) => #abiCallData ( "readDir" , ( #string ( V0_path ) , ( #uint64 ( V1_maxDepth ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , V1_maxDepth )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadDir ( V0_path : string , V1_maxDepth : uint64 , V2_followLinks : bool ) => #abiCallData ( "readDir" , ( #string ( V0_path ) , ( #uint64 ( V1_maxDepth ) , ( #bool ( V2_followLinks ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , V1_maxDepth )
       andBool ( #rangeBool ( V2_followLinks )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadFile ( V0_path : string ) => #abiCallData ( "readFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadFileBinary ( V0_path : string ) => #abiCallData ( "readFileBinary" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadLine ( V0_path : string ) => #abiCallData ( "readLine" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KreadLink ( V0_linkPath : string ) => #abiCallData ( "readLink" , ( #string ( V0_linkPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Krecord ( ) => #abiCallData ( "record" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrecordLogs ( ) => #abiCallData ( "recordLogs" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrememberKey ( V0_privateKey : uint256 ) => #abiCallData ( "rememberKey" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KremoveDir ( V0_path : string , V1_recursive : bool ) => #abiCallData ( "removeDir" , ( #string ( V0_path ) , ( #bool ( V1_recursive ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_recursive )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KremoveFile ( V0_path : string ) => #abiCallData ( "removeFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kreplace ( V0_input : string , V1_from : string , V2_to : string ) => #abiCallData ( "replace" , ( #string ( V0_input ) , ( #string ( V1_from ) , ( #string ( V2_to ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KresetNonce ( V0_account : address ) => #abiCallData ( "resetNonce" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KresumeGasMetering ( ) => #abiCallData ( "resumeGasMetering" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrevertTo ( V0_snapshotId : uint256 ) => #abiCallData ( "revertTo" , ( #uint256 ( V0_snapshotId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_snapshotId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrevertToAndDelete ( V0_snapshotId : uint256 ) => #abiCallData ( "revertToAndDelete" , ( #uint256 ( V0_snapshotId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_snapshotId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrevokePersistent ( V0_account : address ) => #abiCallData ( "revokePersistent" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrevokePersistent ( V0_accounts_0 : address , V0_accounts_1 : address ) => #abiCallData ( "revokePersistent" , ( #array ( #address ( V0_accounts_0 ) , 2 , ( #address ( V0_accounts_0 ) , ( #address ( V0_accounts_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_accounts_0 )
       andBool ( #rangeAddress ( V0_accounts_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kroll ( V0_newHeight : uint256 ) => #abiCallData ( "roll" , ( #uint256 ( V0_newHeight ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newHeight )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrollFork ( V0_txHash : bytes32 ) => #abiCallData ( "rollFork" , ( #bytes32 ( V0_txHash ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_txHash )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrollFork ( V0_blockNumber : uint256 ) => #abiCallData ( "rollFork" , ( #uint256 ( V0_blockNumber ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_blockNumber )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrollFork ( V0_forkId : uint256 , V1_txHash : bytes32 ) => #abiCallData ( "rollFork" , ( #uint256 ( V0_forkId ) , ( #bytes32 ( V1_txHash ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_forkId )
       andBool ( #rangeBytes ( 32 , V1_txHash )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrollFork ( V0_forkId : uint256 , V1_blockNumber : uint256 ) => #abiCallData ( "rollFork" , ( #uint256 ( V0_forkId ) , ( #uint256 ( V1_blockNumber ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_forkId )
       andBool ( #rangeUInt ( 256 , V1_blockNumber )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Krpc ( V0_method : string , V1_params : string ) => #abiCallData ( "rpc" , ( #string ( V0_method ) , ( #string ( V1_params ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Krpc ( V0_urlOrAlias : string , V1_method : string , V2_params : string ) => #abiCallData ( "rpc" , ( #string ( V0_urlOrAlias ) , ( #string ( V1_method ) , ( #string ( V2_params ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrpcUrl ( V0_rpcAlias : string ) => #abiCallData ( "rpcUrl" , ( #string ( V0_rpcAlias ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrpcUrlStructs ( ) => #abiCallData ( "rpcUrlStructs" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KrpcUrls ( ) => #abiCallData ( "rpcUrls" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KselectFork ( V0_forkId : uint256 ) => #abiCallData ( "selectFork" , ( #uint256 ( V0_forkId ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_forkId )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeAddress ( V0_objectKey : string , V1_valueKey : string , V2_value : address ) => #abiCallData ( "serializeAddress" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #address ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeAddress ( V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeAddress ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : address , V2_values_1 : address ) => #abiCallData ( "serializeAddress" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #address ( V2_values_0 ) , 2 , ( #address ( V2_values_0 ) , ( #address ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V2_values_0 )
       andBool ( #rangeAddress ( V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeBool ( V0_objectKey : string , V1_valueKey : string , V2_value : bool ) => #abiCallData ( "serializeBool" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #bool ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeBool ( V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeBool ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : bool , V2_values_1 : bool ) => #abiCallData ( "serializeBool" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #bool ( V2_values_0 ) , 2 , ( #bool ( V2_values_0 ) , ( #bool ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V2_values_0 )
       andBool ( #rangeBool ( V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeBytes ( V0_objectKey : string , V1_valueKey : string , V2_value : bytes ) => #abiCallData ( "serializeBytes" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #bytes ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V2_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeBytes ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : bytes , V2_values_1 : bytes ) => #abiCallData ( "serializeBytes" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #bytes ( V2_values_0 ) , 2 , ( #bytes ( V2_values_0 ) , ( #bytes ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V2_values_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_values_1 ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeBytes32 ( V0_objectKey : string , V1_valueKey : string , V2_value : bytes32 ) => #abiCallData ( "serializeBytes32" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #bytes32 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeBytes ( 32 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeBytes32 ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : bytes32 , V2_values_1 : bytes32 ) => #abiCallData ( "serializeBytes32" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #bytes32 ( V2_values_0 ) , 2 , ( #bytes32 ( V2_values_0 ) , ( #bytes32 ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V2_values_0 )
       andBool ( #rangeBytes ( 32 , V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeInt ( V0_objectKey : string , V1_valueKey : string , V2_value : int256 ) => #abiCallData ( "serializeInt" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #int256 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeSInt ( 256 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeInt ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : int256 , V2_values_1 : int256 ) => #abiCallData ( "serializeInt" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #int256 ( V2_values_0 ) , 2 , ( #int256 ( V2_values_0 ) , ( #int256 ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V2_values_0 )
       andBool ( #rangeSInt ( 256 , V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeJson ( V0_objectKey : string , V1_value : string ) => #abiCallData ( "serializeJson" , ( #string ( V0_objectKey ) , ( #string ( V1_value ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeJsonType ( V0_typeDescription : string , V1_value : bytes ) => #abiCallData ( "serializeJsonType" , ( #string ( V0_typeDescription ) , ( #bytes ( V1_value ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeJsonType ( V0_objectKey : string , V1_valueKey : string , V2_typeDescription : string , V3_value : bytes ) => #abiCallData ( "serializeJsonType" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #string ( V2_typeDescription ) , ( #bytes ( V3_value ) , .TypedArgs ) ) ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V3_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeString ( V0_objectKey : string , V1_valueKey : string , V2_value : string ) => #abiCallData ( "serializeString" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #string ( V2_value ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeString ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : string , V2_values_1 : string ) => #abiCallData ( "serializeString" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #string ( V2_values_0 ) , 2 , ( #string ( V2_values_0 ) , ( #string ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeUint ( V0_objectKey : string , V1_valueKey : string , V2_value : uint256 ) => #abiCallData ( "serializeUint" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #uint256 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 256 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeUint ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : uint256 , V2_values_1 : uint256 ) => #abiCallData ( "serializeUint" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #uint256 ( V2_values_0 ) , 2 , ( #uint256 ( V2_values_0 ) , ( #uint256 ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V2_values_0 )
       andBool ( #rangeUInt ( 256 , V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KserializeUintToHex ( V0_objectKey : string , V1_valueKey : string , V2_value : uint256 ) => #abiCallData ( "serializeUintToHex" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #uint256 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 256 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsetBlockhash ( V0_blockNumber : uint256 , V1_blockHash : bytes32 ) => #abiCallData ( "setBlockhash" , ( #uint256 ( V0_blockNumber ) , ( #bytes32 ( V1_blockHash ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_blockNumber )
       andBool ( #rangeBytes ( 32 , V1_blockHash )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsetEnv ( V0_name : string , V1_value : string ) => #abiCallData ( "setEnv" , ( #string ( V0_name ) , ( #string ( V1_value ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsetNonce ( V0_account : address , V1_newNonce : uint64 ) => #abiCallData ( "setNonce" , ( #address ( V0_account ) , ( #uint64 ( V1_newNonce ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_account )
       andBool ( #rangeUInt ( 64 , V1_newNonce )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsetNonceUnsafe ( V0_account : address , V1_newNonce : uint64 ) => #abiCallData ( "setNonceUnsafe" , ( #address ( V0_account ) , ( #uint64 ( V1_newNonce ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_account )
       andBool ( #rangeUInt ( 64 , V1_newNonce )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ksign ( V0_addr : address , V1_publicKeyX : uint256 , V2_publicKeyY : uint256 , V3_privateKey : uint256 , V4_digest : bytes32 ) => #abiCallData ( "sign" , ( #tuple ( ( #address ( V0_addr ) , ( #uint256 ( V1_publicKeyX ) , ( #uint256 ( V2_publicKeyY ) , ( #uint256 ( V3_privateKey ) , .TypedArgs ) ) ) ) ) , ( #bytes32 ( V4_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_addr )
       andBool ( #rangeUInt ( 256 , V1_publicKeyX )
       andBool ( #rangeUInt ( 256 , V2_publicKeyY )
       andBool ( #rangeUInt ( 256 , V3_privateKey )
       andBool ( #rangeBytes ( 32 , V4_digest )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ksign ( V0_signer : address , V1_digest : bytes32 ) => #abiCallData ( "sign" , ( #address ( V0_signer ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_signer )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ksign ( V0_digest : bytes32 ) => #abiCallData ( "sign" , ( #bytes32 ( V0_digest ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_digest )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ksign ( V0_privateKey : uint256 , V1_digest : bytes32 ) => #abiCallData ( "sign" , ( #uint256 ( V0_privateKey ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_privateKey )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsignCompact ( V0_addr : address , V1_publicKeyX : uint256 , V2_publicKeyY : uint256 , V3_privateKey : uint256 , V4_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #tuple ( ( #address ( V0_addr ) , ( #uint256 ( V1_publicKeyX ) , ( #uint256 ( V2_publicKeyY ) , ( #uint256 ( V3_privateKey ) , .TypedArgs ) ) ) ) ) , ( #bytes32 ( V4_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_addr )
       andBool ( #rangeUInt ( 256 , V1_publicKeyX )
       andBool ( #rangeUInt ( 256 , V2_publicKeyY )
       andBool ( #rangeUInt ( 256 , V3_privateKey )
       andBool ( #rangeBytes ( 32 , V4_digest )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsignCompact ( V0_signer : address , V1_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #address ( V0_signer ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_signer )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsignCompact ( V0_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #bytes32 ( V0_digest ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_digest )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsignCompact ( V0_privateKey : uint256 , V1_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #uint256 ( V0_privateKey ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_privateKey )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KsignP256 ( V0_privateKey : uint256 , V1_digest : bytes32 ) => #abiCallData ( "signP256" , ( #uint256 ( V0_privateKey ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_privateKey )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kskip ( V0_skipTest : bool ) => #abiCallData ( "skip" , ( #bool ( V0_skipTest ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_skipTest )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ksleep ( V0_duration : uint256 ) => #abiCallData ( "sleep" , ( #uint256 ( V0_duration ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_duration )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ksnapshot ( ) => #abiCallData ( "snapshot" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ksplit ( V0_input : string , V1_delimiter : string ) => #abiCallData ( "split" , ( #string ( V0_input ) , ( #string ( V1_delimiter ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstartBroadcast ( ) => #abiCallData ( "startBroadcast" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstartBroadcast ( V0_signer : address ) => #abiCallData ( "startBroadcast" , ( #address ( V0_signer ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_signer )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstartBroadcast ( V0_privateKey : uint256 ) => #abiCallData ( "startBroadcast" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstartMappingRecording ( ) => #abiCallData ( "startMappingRecording" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstartPrank ( V0_msgSender : address ) => #abiCallData ( "startPrank" , ( #address ( V0_msgSender ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_msgSender )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstartPrank ( V0_msgSender : address , V1_txOrigin : address ) => #abiCallData ( "startPrank" , ( #address ( V0_msgSender ) , ( #address ( V1_txOrigin ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_msgSender )
       andBool ( #rangeAddress ( V1_txOrigin )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstartStateDiffRecording ( ) => #abiCallData ( "startStateDiffRecording" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstopAndReturnStateDiff ( ) => #abiCallData ( "stopAndReturnStateDiff" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstopBroadcast ( ) => #abiCallData ( "stopBroadcast" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstopExpectSafeMemory ( ) => #abiCallData ( "stopExpectSafeMemory" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstopMappingRecording ( ) => #abiCallData ( "stopMappingRecording" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KstopPrank ( ) => #abiCallData ( "stopPrank" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kstore ( V0_target : address , V1_slot : bytes32 , V2_value : bytes32 ) => #abiCallData ( "store" , ( #address ( V0_target ) , ( #bytes32 ( V1_slot ) , ( #bytes32 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_slot )
       andBool ( #rangeBytes ( 32 , V2_value )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoBase64 ( V0_data : bytes ) => #abiCallData ( "toBase64" , ( #bytes ( V0_data ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoBase64 ( V0_data : string ) => #abiCallData ( "toBase64" , ( #string ( V0_data ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoBase64URL ( V0_data : bytes ) => #abiCallData ( "toBase64URL" , ( #bytes ( V0_data ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoBase64URL ( V0_data : string ) => #abiCallData ( "toBase64URL" , ( #string ( V0_data ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoLowercase ( V0_input : string ) => #abiCallData ( "toLowercase" , ( #string ( V0_input ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoString ( V0_value : address ) => #abiCallData ( "toString" , ( #address ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoString ( V0_value : bool ) => #abiCallData ( "toString" , ( #bool ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoString ( V0_value : bytes ) => #abiCallData ( "toString" , ( #bytes ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoString ( V0_value : bytes32 ) => #abiCallData ( "toString" , ( #bytes32 ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoString ( V0_value : int256 ) => #abiCallData ( "toString" , ( #int256 ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeSInt ( 256 , V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoString ( V0_value : uint256 ) => #abiCallData ( "toString" , ( #uint256 ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtoUppercase ( V0_input : string ) => #abiCallData ( "toUppercase" , ( #string ( V0_input ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ktransact ( V0_txHash : bytes32 ) => #abiCallData ( "transact" , ( #bytes32 ( V0_txHash ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_txHash )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ktransact ( V0_forkId : uint256 , V1_txHash : bytes32 ) => #abiCallData ( "transact" , ( #uint256 ( V0_forkId ) , ( #bytes32 ( V1_txHash ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_forkId )
       andBool ( #rangeBytes ( 32 , V1_txHash )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Ktrim ( V0_input : string ) => #abiCallData ( "trim" , ( #string ( V0_input ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtryFfi ( V0_commandInput_0 : string , V0_commandInput_1 : string ) => #abiCallData ( "tryFfi" , ( #array ( #string ( V0_commandInput_0 ) , 2 , ( #string ( V0_commandInput_0 ) , ( #string ( V0_commandInput_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KtxGasPrice ( V0_newGasPrice : uint256 ) => #abiCallData ( "txGasPrice" , ( #uint256 ( V0_newGasPrice ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newGasPrice )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KunixTime ( ) => #abiCallData ( "unixTime" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2Kwarp ( V0_newTimestamp : uint256 ) => #abiCallData ( "warp" , ( #uint256 ( V0_newTimestamp ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_newTimestamp )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KwriteFile ( V0_path : string , V1_data : string ) => #abiCallData ( "writeFile" , ( #string ( V0_path ) , ( #string ( V1_data ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KwriteFileBinary ( V0_path : string , V1_data : bytes ) => #abiCallData ( "writeFileBinary" , ( #string ( V0_path ) , ( #bytes ( V1_data ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KwriteJson ( V0_json : string , V1_path : string ) => #abiCallData ( "writeJson" , ( #string ( V0_json ) , ( #string ( V1_path ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KwriteJson ( V0_json : string , V1_path : string , V2_valueKey : string ) => #abiCallData ( "writeJson" , ( #string ( V0_json ) , ( #string ( V1_path ) , ( #string ( V2_valueKey ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KwriteLine ( V0_path : string , V1_data : string ) => #abiCallData ( "writeLine" , ( #string ( V0_path ) , ( #string ( V1_data ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KwriteToml ( V0_json : string , V1_path : string ) => #abiCallData ( "writeToml" , ( #string ( V0_json ) , ( #string ( V1_path ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVm . S2KwriteToml ( V0_json : string , V1_path : string , V2_valueKey : string ) => #abiCallData ( "writeToml" , ( #string ( V0_json ) , ( #string ( V1_path ) , ( #string ( V2_valueKey ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( selector ( "accesses(address)" ) => 1706857601 )
      
    
    rule  ( selector ( "activeFork()" ) => 789593890 )
      
    
    rule  ( selector ( "addr(uint256)" ) => 4288775753 )
      
    
    rule  ( selector ( "allowCheatcodes(address)" ) => 3926262417 )
      
    
    rule  ( selector ( "assertApproxEqAbs(int256,int256,uint256)" ) => 604996509 )
      
    
    rule  ( selector ( "assertApproxEqAbs(int256,int256,uint256,string)" ) => 2190075425 )
      
    
    rule  ( selector ( "assertApproxEqAbs(uint256,uint256,uint256)" ) => 382863302 )
      
    
    rule  ( selector ( "assertApproxEqAbs(uint256,uint256,uint256,string)" ) => 4145066082 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(int256,int256,uint256,uint256)" ) => 1029425340 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(int256,int256,uint256,uint256,string)" ) => 1783654100 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(uint256,uint256,uint256,uint256)" ) => 73160142 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(uint256,uint256,uint256,uint256,string)" ) => 1614978738 )
      
    
    rule  ( selector ( "assertApproxEqRel(int256,int256,uint256)" ) => 4272083279 )
      
    
    rule  ( selector ( "assertApproxEqRel(int256,int256,uint256,string)" ) => 4012342642 )
      
    
    rule  ( selector ( "assertApproxEqRel(uint256,uint256,uint256)" ) => 2364694260 )
      
    
    rule  ( selector ( "assertApproxEqRel(uint256,uint256,uint256,string)" ) => 516652339 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(int256,int256,uint256,uint256)" ) => 2881429964 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(int256,int256,uint256,uint256,string)" ) => 4241232324 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(uint256,uint256,uint256,uint256)" ) => 569190775 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(uint256,uint256,uint256,uint256,string)" ) => 2195114237 )
      
    
    rule  ( selector ( "assertEq(address,address)" ) => 1364419062 )
      
    
    rule  ( selector ( "assertEq(address,address,string)" ) => 791112145 )
      
    
    rule  ( selector ( "assertEq(address[],address[])" ) => 946383924 )
      
    
    rule  ( selector ( "assertEq(address[],address[],string)" ) => 1049719749 )
      
    
    rule  ( selector ( "assertEq(bool,bool)" ) => 4160631927 )
      
    
    rule  ( selector ( "assertEq(bool,bool,string)" ) => 1303486078 )
      
    
    rule  ( selector ( "assertEq(bool[],bool[])" ) => 1887303557 )
      
    
    rule  ( selector ( "assertEq(bool[],bool[],string)" ) => 3834285965 )
      
    
    rule  ( selector ( "assertEq(bytes,bytes)" ) => 2539800113 )
      
    
    rule  ( selector ( "assertEq(bytes,bytes,string)" ) => 3796888832 )
      
    
    rule  ( selector ( "assertEq(bytes32,bytes32)" ) => 2089076379 )
      
    
    rule  ( selector ( "assertEq(bytes32,bytes32,string)" ) => 3254394576 )
      
    
    rule  ( selector ( "assertEq(bytes32[],bytes32[])" ) => 214560388 )
      
    
    rule  ( selector ( "assertEq(bytes32[],bytes32[],string)" ) => 3762196855 )
      
    
    rule  ( selector ( "assertEq(bytes[],bytes[])" ) => 3858471754 )
      
    
    rule  ( selector ( "assertEq(bytes[],bytes[],string)" ) => 4094947510 )
      
    
    rule  ( selector ( "assertEq(int256,int256)" ) => 4269076571 )
      
    
    rule  ( selector ( "assertEq(int256,int256,string)" ) => 1900687123 )
      
    
    rule  ( selector ( "assertEq(int256[],int256[])" ) => 1896891308 )
      
    
    rule  ( selector ( "assertEq(int256[],int256[],string)" ) => 421468976 )
      
    
    rule  ( selector ( "assertEq(string,string)" ) => 4079016291 )
      
    
    rule  ( selector ( "assertEq(string,string,string)" ) => 922113752 )
      
    
    rule  ( selector ( "assertEq(string[],string[])" ) => 3474719900 )
      
    
    rule  ( selector ( "assertEq(string[],string[],string)" ) => 4025922173 )
      
    
    rule  ( selector ( "assertEq(uint256,uint256)" ) => 2552851540 )
      
    
    rule  ( selector ( "assertEq(uint256,uint256,string)" ) => 2293517445 )
      
    
    rule  ( selector ( "assertEq(uint256[],uint256[])" ) => 2539477522 )
      
    
    rule  ( selector ( "assertEq(uint256[],uint256[],string)" ) => 1561904954 )
      
    
    rule  ( selector ( "assertEqDecimal(int256,int256,uint256)" ) => 1208052740 )
      
    
    rule  ( selector ( "assertEqDecimal(int256,int256,uint256,string)" ) => 2121773253 )
      
    
    rule  ( selector ( "assertEqDecimal(uint256,uint256,uint256)" ) => 665812380 )
      
    
    rule  ( selector ( "assertEqDecimal(uint256,uint256,uint256,string)" ) => 3503013359 )
      
    
    rule  ( selector ( "assertFalse(bool)" ) => 2778212485 )
      
    
    rule  ( selector ( "assertFalse(bool,string)" ) => 2074101769 )
      
    
    rule  ( selector ( "assertGe(int256,int256)" ) => 170964849 )
      
    
    rule  ( selector ( "assertGe(int256,int256,string)" ) => 2822973661 )
      
    
    rule  ( selector ( "assertGe(uint256,uint256)" ) => 2832519641 )
      
    
    rule  ( selector ( "assertGe(uint256,uint256,string)" ) => 3797041856 )
      
    
    rule  ( selector ( "assertGeDecimal(int256,int256,uint256)" ) => 3693658353 )
      
    
    rule  ( selector ( "assertGeDecimal(int256,int256,uint256,string)" ) => 1576615067 )
      
    
    rule  ( selector ( "assertGeDecimal(uint256,uint256,uint256)" ) => 1025499274 )
      
    
    rule  ( selector ( "assertGeDecimal(uint256,uint256,uint256,string)" ) => 2348781875 )
      
    
    rule  ( selector ( "assertGt(int256,int256)" ) => 1513499973 )
      
    
    rule  ( selector ( "assertGt(int256,int256,string)" ) => 4174592923 )
      
    
    rule  ( selector ( "assertGt(uint256,uint256)" ) => 3674733778 )
      
    
    rule  ( selector ( "assertGt(uint256,uint256,string)" ) => 3651388626 )
      
    
    rule  ( selector ( "assertGtDecimal(int256,int256,uint256)" ) => 2019630862 )
      
    
    rule  ( selector ( "assertGtDecimal(int256,int256,uint256,string)" ) => 77973419 )
      
    
    rule  ( selector ( "assertGtDecimal(uint256,uint256,uint256)" ) => 3972867127 )
      
    
    rule  ( selector ( "assertGtDecimal(uint256,uint256,uint256,string)" ) => 1687460493 )
      
    
    rule  ( selector ( "assertLe(int256,int256)" ) => 2516391246 )
      
    
    rule  ( selector ( "assertLe(int256,int256,string)" ) => 1308518700 )
      
    
    rule  ( selector ( "assertLe(uint256,uint256)" ) => 2221339669 )
      
    
    rule  ( selector ( "assertLe(uint256,uint256,string)" ) => 3514649357 )
      
    
    rule  ( selector ( "assertLeDecimal(int256,int256,uint256)" ) => 298923594 )
      
    
    rule  ( selector ( "assertLeDecimal(int256,int256,uint256,string)" ) => 2858219400 )
      
    
    rule  ( selector ( "assertLeDecimal(uint256,uint256,uint256)" ) => 3271862967 )
      
    
    rule  ( selector ( "assertLeDecimal(uint256,uint256,uint256,string)" ) => 2146417632 )
      
    
    rule  ( selector ( "assertLt(int256,int256)" ) => 1049706624 )
      
    
    rule  ( selector ( "assertLt(int256,int256,string)" ) => 2683646435 )
      
    
    rule  ( selector ( "assertLt(uint256,uint256)" ) => 2972696581 )
      
    
    rule  ( selector ( "assertLt(uint256,uint256,string)" ) => 1708507445 )
      
    
    rule  ( selector ( "assertLtDecimal(int256,int256,uint256)" ) => 3689470091 )
      
    
    rule  ( selector ( "assertLtDecimal(int256,int256,uint256,string)" ) => 1089516768 )
      
    
    rule  ( selector ( "assertLtDecimal(uint256,uint256,uint256)" ) => 544682878 )
      
    
    rule  ( selector ( "assertLtDecimal(uint256,uint256,uint256,string)" ) => 2842873911 )
      
    
    rule  ( selector ( "assertNotEq(address,address)" ) => 2972587668 )
      
    
    rule  ( selector ( "assertNotEq(address,address,string)" ) => 2272634257 )
      
    
    rule  ( selector ( "assertNotEq(address[],address[])" ) => 1188082258 )
      
    
    rule  ( selector ( "assertNotEq(address[],address[],string)" ) => 1925701813 )
      
    
    rule  ( selector ( "assertNotEq(bool,bool)" ) => 594431334 )
      
    
    rule  ( selector ( "assertNotEq(bool,bool,string)" ) => 277979745 )
      
    
    rule  ( selector ( "assertNotEq(bool[],bool[])" ) => 678408170 )
      
    
    rule  ( selector ( "assertNotEq(bool[],bool[],string)" ) => 1657207291 )
      
    
    rule  ( selector ( "assertNotEq(bytes,bytes)" ) => 1022856744 )
      
    
    rule  ( selector ( "assertNotEq(bytes,bytes,string)" ) => 2500285454 )
      
    
    rule  ( selector ( "assertNotEq(bytes32,bytes32)" ) => 2307818492 )
      
    
    rule  ( selector ( "assertNotEq(bytes32,bytes32,string)" ) => 2989698897 )
      
    
    rule  ( selector ( "assertNotEq(bytes32[],bytes32[])" ) => 100919912 )
      
    
    rule  ( selector ( "assertNotEq(bytes32[],bytes32[],string)" ) => 3094569804 )
      
    
    rule  ( selector ( "assertNotEq(bytes[],bytes[])" ) => 3991719989 )
      
    
    rule  ( selector ( "assertNotEq(bytes[],bytes[],string)" ) => 499982184 )
      
    
    rule  ( selector ( "assertNotEq(int256,int256)" ) => 4106224867 )
      
    
    rule  ( selector ( "assertNotEq(int256,int256,string)" ) => 1193592249 )
      
    
    rule  ( selector ( "assertNotEq(int256[],int256[])" ) => 192083183 )
      
    
    rule  ( selector ( "assertNotEq(int256[],int256[],string)" ) => 3549917986 )
      
    
    rule  ( selector ( "assertNotEq(string,string)" ) => 1786918835 )
      
    
    rule  ( selector ( "assertNotEq(string,string,string)" ) => 2025705127 )
      
    
    rule  ( selector ( "assertNotEq(string[],string[])" ) => 3187330024 )
      
    
    rule  ( selector ( "assertNotEq(string[],string[],string)" ) => 3060893683 )
      
    
    rule  ( selector ( "assertNotEq(uint256,uint256)" ) => 3079705376 )
      
    
    rule  ( selector ( "assertNotEq(uint256,uint256,string)" ) => 2566503869 )
      
    
    rule  ( selector ( "assertNotEq(uint256[],uint256[])" ) => 1458740410 )
      
    
    rule  ( selector ( "assertNotEq(uint256[],uint256[],string)" ) => 2592062863 )
      
    
    rule  ( selector ( "assertNotEqDecimal(int256,int256,uint256)" ) => 350705280 )
      
    
    rule  ( selector ( "assertNotEqDecimal(int256,int256,uint256,string)" ) => 865378059 )
      
    
    rule  ( selector ( "assertNotEqDecimal(uint256,uint256,uint256)" ) => 1721695399 )
      
    
    rule  ( selector ( "assertNotEqDecimal(uint256,uint256,uint256,string)" ) => 4121253208 )
      
    
    rule  ( selector ( "assertTrue(bool)" ) => 211801473 )
      
    
    rule  ( selector ( "assertTrue(bool,string)" ) => 2739854339 )
      
    
    rule  ( selector ( "assume(bool)" ) => 1281615202 )
      
    
    rule  ( selector ( "blobBaseFee(uint256)" ) => 1831951742 )
      
    
    rule  ( selector ( "blobhashes(bytes32[])" ) => 312338411 )
      
    
    rule  ( selector ( "breakpoint(string)" ) => 4028997266 )
      
    
    rule  ( selector ( "breakpoint(string,bool)" ) => 4157840013 )
      
    
    rule  ( selector ( "broadcast()" ) => 2949218368 )
      
    
    rule  ( selector ( "broadcast(address)" ) => 3868601563 )
      
    
    rule  ( selector ( "broadcast(uint256)" ) => 4135229019 )
      
    
    rule  ( selector ( "broadcastRawTransaction(bytes)" ) => 2349626080 )
      
    
    rule  ( selector ( "chainId(uint256)" ) => 1078582738 )
      
    
    rule  ( selector ( "clearMockedCalls()" ) => 1071599125 )
      
    
    rule  ( selector ( "closeFile(string)" ) => 1220748319 )
      
    
    rule  ( selector ( "coinbase(address)" ) => 4282924116 )
      
    
    rule  ( selector ( "computeCreate2Address(bytes32,bytes32)" ) => 2299275323 )
      
    
    rule  ( selector ( "computeCreate2Address(bytes32,bytes32,address)" ) => 3542319722 )
      
    
    rule  ( selector ( "computeCreateAddress(address,uint256)" ) => 1952676474 )
      
    
    rule  ( selector ( "copyFile(string,string)" ) => 2773125080 )
      
    
    rule  ( selector ( "createDir(string,bool)" ) => 378234067 )
      
    
    rule  ( selector ( "createFork(string)" ) => 834286744 )
      
    
    rule  ( selector ( "createFork(string,bytes32)" ) => 2091030146 )
      
    
    rule  ( selector ( "createFork(string,uint256)" ) => 1805892139 )
      
    
    rule  ( selector ( "createSelectFork(string)" ) => 2556952628 )
      
    
    rule  ( selector ( "createSelectFork(string,bytes32)" ) => 2228562810 )
      
    
    rule  ( selector ( "createSelectFork(string,uint256)" ) => 1911440973 )
      
    
    rule  ( selector ( "createWallet(string)" ) => 1946481106 )
      
    
    rule  ( selector ( "createWallet(uint256)" ) => 2053594038 )
      
    
    rule  ( selector ( "createWallet(uint256,string)" ) => 3984348258 )
      
    
    rule  ( selector ( "deal(address,uint256)" ) => 3364511341 )
      
    
    rule  ( selector ( "deleteSnapshot(uint256)" ) => 2788590935 )
      
    
    rule  ( selector ( "deleteSnapshots()" ) => 1109058665 )
      
    
    rule  ( selector ( "deployCode(string)" ) => 2592286112 )
      
    
    rule  ( selector ( "deployCode(string,bytes)" ) => 701406686 )
      
    
    rule  ( selector ( "deriveKey(string,string,uint32)" ) => 1808477211 )
      
    
    rule  ( selector ( "deriveKey(string,string,uint32,string)" ) => 690174751 )
      
    
    rule  ( selector ( "deriveKey(string,uint32)" ) => 1646872971 )
      
    
    rule  ( selector ( "deriveKey(string,uint32,string)" ) => 851973997 )
      
    
    rule  ( selector ( "difficulty(uint256)" ) => 1187812057 )
      
    
    rule  ( selector ( "dumpState(string)" ) => 1889455423 )
      
    
    rule  ( selector ( "ensNamehash(string)" ) => 2352434277 )
      
    
    rule  ( selector ( "envAddress(string)" ) => 890066623 )
      
    
    rule  ( selector ( "envAddress(string,string)" ) => 2905717242 )
      
    
    rule  ( selector ( "envBool(string)" ) => 2127686781 )
      
    
    rule  ( selector ( "envBool(string,string)" ) => 2863521455 )
      
    
    rule  ( selector ( "envBytes(string)" ) => 1299951366 )
      
    
    rule  ( selector ( "envBytes(string,string)" ) => 3720504603 )
      
    
    rule  ( selector ( "envBytes32(string)" ) => 2543095874 )
      
    
    rule  ( selector ( "envBytes32(string,string)" ) => 1525821889 )
      
    
    rule  ( selector ( "envExists(string)" ) => 3464717817 )
      
    
    rule  ( selector ( "envInt(string)" ) => 2301234273 )
      
    
    rule  ( selector ( "envInt(string,string)" ) => 1108873552 )
      
    
    rule  ( selector ( "envOr(string,address)" ) => 1444930880 )
      
    
    rule  ( selector ( "envOr(string,bool)" ) => 1199043535 )
      
    
    rule  ( selector ( "envOr(string,bytes)" ) => 3018094341 )
      
    
    rule  ( selector ( "envOr(string,bytes32)" ) => 3030931602 )
      
    
    rule  ( selector ( "envOr(string,int256)" ) => 3150672190 )
      
    
    rule  ( selector ( "envOr(string,string)" ) => 3510989676 )
      
    
    rule  ( selector ( "envOr(string,string,address[])" ) => 3343818219 )
      
    
    rule  ( selector ( "envOr(string,string,bool[])" ) => 3951421499 )
      
    
    rule  ( selector ( "envOr(string,string,bytes32[])" ) => 578941799 )
      
    
    rule  ( selector ( "envOr(string,string,bytes[])" ) => 1690058340 )
      
    
    rule  ( selector ( "envOr(string,string,int256[])" ) => 1191237451 )
      
    
    rule  ( selector ( "envOr(string,string,string[])" ) => 2240943804 )
      
    
    rule  ( selector ( "envOr(string,string,uint256[])" ) => 1949402408 )
      
    
    rule  ( selector ( "envOr(string,uint256)" ) => 1586967695 )
      
    
    rule  ( selector ( "envString(string)" ) => 4168600345 )
      
    
    rule  ( selector ( "envString(string,string)" ) => 347089865 )
      
    
    rule  ( selector ( "envUint(string)" ) => 3247934751 )
      
    
    rule  ( selector ( "envUint(string,string)" ) => 4091461785 )
      
    
    rule  ( selector ( "etch(address,bytes)" ) => 3033974658 )
      
    
    rule  ( selector ( "eth_getLogs(uint256,uint256,address,bytes32[])" ) => 903951515 )
      
    
    rule  ( selector ( "exists(string)" ) => 639251006 )
      
    
    rule  ( selector ( "expectCall(address,bytes)" ) => 3177903156 )
      
    
    rule  ( selector ( "expectCall(address,bytes,uint64)" ) => 3249388543 )
      
    
    rule  ( selector ( "expectCall(address,uint256,bytes)" ) => 4077681571 )
      
    
    rule  ( selector ( "expectCall(address,uint256,bytes,uint64)" ) => 2729550254 )
      
    
    rule  ( selector ( "expectCall(address,uint256,uint64,bytes)" ) => 590746119 )
      
    
    rule  ( selector ( "expectCall(address,uint256,uint64,bytes,uint64)" ) => 1706538956 )
      
    
    rule  ( selector ( "expectCallMinGas(address,uint256,uint64,bytes)" ) => 149217558 )
      
    
    rule  ( selector ( "expectCallMinGas(address,uint256,uint64,bytes,uint64)" ) => 3778680884 )
      
    
    rule  ( selector ( "expectEmit()" ) => 1141821709 )
      
    
    rule  ( selector ( "expectEmit(address)" ) => 2260296205 )
      
    
    rule  ( selector ( "expectEmit(bool,bool,bool,bool)" ) => 1226622914 )
      
    
    rule  ( selector ( "expectEmit(bool,bool,bool,bool,address)" ) => 2176505587 )
      
    
    rule  ( selector ( "expectEmitAnonymous()" ) => 777987852 )
      
    
    rule  ( selector ( "expectEmitAnonymous(address)" ) => 1875281669 )
      
    
    rule  ( selector ( "expectEmitAnonymous(bool,bool,bool,bool,bool)" ) => 3376995166 )
      
    
    rule  ( selector ( "expectEmitAnonymous(bool,bool,bool,bool,bool,address)" ) => 1909020825 )
      
    
    rule  ( selector ( "expectRevert()" ) => 4102309908 )
      
    
    rule  ( selector ( "expectRevert(bytes)" ) => 4069379763 )
      
    
    rule  ( selector ( "expectRevert(bytes4)" ) => 3273568480 )
      
    
    rule  ( selector ( "expectSafeMemory(uint64,uint64)" ) => 1828808328 )
      
    
    rule  ( selector ( "expectSafeMemoryCall(uint64,uint64)" ) => 92507124 )
      
    
    rule  ( selector ( "fee(uint256)" ) => 968063664 )
      
    
    rule  ( selector ( "ffi(string[])" ) => 2299921511 )
      
    
    rule  ( selector ( "fsMetadata(string)" ) => 2939587080 )
      
    
    rule  ( selector ( "getBlobBaseFee()" ) => 527265527 )
      
    
    rule  ( selector ( "getBlobhashes()" ) => 4117754251 )
      
    
    rule  ( selector ( "getBlockNumber()" ) => 1120645468 )
      
    
    rule  ( selector ( "getBlockTimestamp()" ) => 2037090745 )
      
    
    rule  ( selector ( "getCode(string)" ) => 2367473957 )
      
    
    rule  ( selector ( "getDeployedCode(string)" ) => 1052734388 )
      
    
    rule  ( selector ( "getFoundryVersion()" ) => 3935902645 )
      
    
    rule  ( selector ( "getLabel(address)" ) => 681724336 )
      
    
    rule  ( selector ( "getMappingKeyAndParentOf(address,bytes32)" ) => 2272142566 )
      
    
    rule  ( selector ( "getMappingLength(address,bytes32)" ) => 791664191 )
      
    
    rule  ( selector ( "getMappingSlotAt(address,bytes32,uint256)" ) => 3955702452 )
      
    
    rule  ( selector ( "getNonce((address,uint256,uint256,uint256))" ) => 2775878317 )
      
    
    rule  ( selector ( "getNonce(address)" ) => 755185067 )
      
    
    rule  ( selector ( "getRecordedLogs()" ) => 420828068 )
      
    
    rule  ( selector ( "indexOf(string,string)" ) => 2315782071 )
      
    
    rule  ( selector ( "isContext(uint8)" ) => 1689199965 )
      
    
    rule  ( selector ( "isDir(string)" ) => 2098581529 )
      
    
    rule  ( selector ( "isFile(string)" ) => 3773498580 )
      
    
    rule  ( selector ( "isPersistent(address)" ) => 3643641597 )
      
    
    rule  ( selector ( "keyExists(string,string)" ) => 1384802364 )
      
    
    rule  ( selector ( "keyExistsJson(string,string)" ) => 3678549494 )
      
    
    rule  ( selector ( "keyExistsToml(string,string)" ) => 1611203501 )
      
    
    rule  ( selector ( "label(address,string)" ) => 3327641368 )
      
    
    rule  ( selector ( "lastCallGas()" ) => 727227176 )
      
    
    rule  ( selector ( "load(address,bytes32)" ) => 1719639408 )
      
    
    rule  ( selector ( "loadAllocs(string)" ) => 3013629655 )
      
    
    rule  ( selector ( "makePersistent(address)" ) => 1474440670 )
      
    
    rule  ( selector ( "makePersistent(address,address)" ) => 1081401512 )
      
    
    rule  ( selector ( "makePersistent(address,address,address)" ) => 4021779061 )
      
    
    rule  ( selector ( "makePersistent(address[])" ) => 496903838 )
      
    
    rule  ( selector ( "mockCall(address,bytes,bytes)" ) => 3110212580 )
      
    
    rule  ( selector ( "mockCall(address,uint256,bytes,bytes)" ) => 2168494993 )
      
    
    rule  ( selector ( "mockCallRevert(address,bytes,bytes)" ) => 3685404999 )
      
    
    rule  ( selector ( "mockCallRevert(address,uint256,bytes,bytes)" ) => 3527200823 )
      
    
    rule  ( selector ( "parseAddress(string)" ) => 3335390621 )
      
    
    rule  ( selector ( "parseBool(string)" ) => 2538535204 )
      
    
    rule  ( selector ( "parseBytes(string)" ) => 2405245741 )
      
    
    rule  ( selector ( "parseBytes32(string)" ) => 142503553 )
      
    
    rule  ( selector ( "parseInt(string)" ) => 1110731870 )
      
    
    rule  ( selector ( "parseJson(string)" ) => 1786929162 )
      
    
    rule  ( selector ( "parseJson(string,string)" ) => 2241072881 )
      
    
    rule  ( selector ( "parseJsonAddress(string,string)" ) => 505013847 )
      
    
    rule  ( selector ( "parseJsonAddressArray(string,string)" ) => 802060419 )
      
    
    rule  ( selector ( "parseJsonBool(string,string)" ) => 2676415633 )
      
    
    rule  ( selector ( "parseJsonBoolArray(string,string)" ) => 2448669007 )
      
    
    rule  ( selector ( "parseJsonBytes(string,string)" ) => 4254211048 )
      
    
    rule  ( selector ( "parseJsonBytes32(string,string)" ) => 393733533 )
      
    
    rule  ( selector ( "parseJsonBytes32Array(string,string)" ) => 2445761475 )
      
    
    rule  ( selector ( "parseJsonBytesArray(string,string)" ) => 1714530969 )
      
    
    rule  ( selector ( "parseJsonInt(string,string)" ) => 2063895757 )
      
    
    rule  ( selector ( "parseJsonIntArray(string,string)" ) => 2575549066 )
      
    
    rule  ( selector ( "parseJsonKeys(string,string)" ) => 557728152 )
      
    
    rule  ( selector ( "parseJsonString(string,string)" ) => 1237646024 )
      
    
    rule  ( selector ( "parseJsonStringArray(string,string)" ) => 1234164980 )
      
    
    rule  ( selector ( "parseJsonType(string,string)" ) => 2849648955 )
      
    
    rule  ( selector ( "parseJsonType(string,string,string)" ) => 3824528947 )
      
    
    rule  ( selector ( "parseJsonTypeArray(string,string,string)" ) => 24499509 )
      
    
    rule  ( selector ( "parseJsonUint(string,string)" ) => 2916999862 )
      
    
    rule  ( selector ( "parseJsonUintArray(string,string)" ) => 1377858731 )
      
    
    rule  ( selector ( "parseToml(string)" ) => 1495355888 )
      
    
    rule  ( selector ( "parseToml(string,string)" ) => 930311688 )
      
    
    rule  ( selector ( "parseTomlAddress(string,string)" ) => 1709688900 )
      
    
    rule  ( selector ( "parseTomlAddressArray(string,string)" ) => 1707354343 )
      
    
    rule  ( selector ( "parseTomlBool(string,string)" ) => 3540897494 )
      
    
    rule  ( selector ( "parseTomlBoolArray(string,string)" ) => 310181530 )
      
    
    rule  ( selector ( "parseTomlBytes(string,string)" ) => 3615227321 )
      
    
    rule  ( selector ( "parseTomlBytes32(string,string)" ) => 2384545808 )
      
    
    rule  ( selector ( "parseTomlBytes32Array(string,string)" ) => 1047621505 )
      
    
    rule  ( selector ( "parseTomlBytesArray(string,string)" ) => 2979512903 )
      
    
    rule  ( selector ( "parseTomlInt(string,string)" ) => 3241477945 )
      
    
    rule  ( selector ( "parseTomlIntArray(string,string)" ) => 3545377510 )
      
    
    rule  ( selector ( "parseTomlKeys(string,string)" ) => 2167030962 )
      
    
    rule  ( selector ( "parseTomlString(string,string)" ) => 2344148291 )
      
    
    rule  ( selector ( "parseTomlStringArray(string,string)" ) => 2674037377 )
      
    
    rule  ( selector ( "parseTomlUint(string,string)" ) => 3430614151 )
      
    
    rule  ( selector ( "parseTomlUintArray(string,string)" ) => 3051300808 )
      
    
    rule  ( selector ( "parseUint(string)" ) => 4203824461 )
      
    
    rule  ( selector ( "pauseGasMetering()" ) => 3517297519 )
      
    
    rule  ( selector ( "prank(address)" ) => 3395723175 )
      
    
    rule  ( selector ( "prank(address,address)" ) => 1206193358 )
      
    
    rule  ( selector ( "prevrandao(bytes32)" ) => 999445833 )
      
    
    rule  ( selector ( "prevrandao(uint256)" ) => 2628894932 )
      
    
    rule  ( selector ( "projectRoot()" ) => 3643842790 )
      
    
    rule  ( selector ( "prompt(string)" ) => 1206580340 )
      
    
    rule  ( selector ( "promptAddress(string)" ) => 1659766260 )
      
    
    rule  ( selector ( "promptSecret(string)" ) => 505912641 )
      
    
    rule  ( selector ( "promptSecretUint(string)" ) => 1774846647 )
      
    
    rule  ( selector ( "promptUint(string)" ) => 1697633417 )
      
    
    rule  ( selector ( "randomAddress()" ) => 3586058741 )
      
    
    rule  ( selector ( "randomUint()" ) => 621954864 )
      
    
    rule  ( selector ( "randomUint(uint256,uint256)" ) => 3592095003 )
      
    
    rule  ( selector ( "readCallers()" ) => 1255193289 )
      
    
    rule  ( selector ( "readDir(string)" ) => 3300678112 )
      
    
    rule  ( selector ( "readDir(string,uint64)" ) => 345474924 )
      
    
    rule  ( selector ( "readDir(string,uint64,bool)" ) => 2164446989 )
      
    
    rule  ( selector ( "readFile(string)" ) => 1626979089 )
      
    
    rule  ( selector ( "readFileBinary(string)" ) => 384662468 )
      
    
    rule  ( selector ( "readLine(string)" ) => 1895126824 )
      
    
    rule  ( selector ( "readLink(string)" ) => 2673247394 )
      
    
    rule  ( selector ( "record()" ) => 644673801 )
      
    
    rule  ( selector ( "recordLogs()" ) => 1101999954 )
      
    
    rule  ( selector ( "rememberKey(uint256)" ) => 571474020 )
      
    
    rule  ( selector ( "removeDir(string,bool)" ) => 1170612241 )
      
    
    rule  ( selector ( "removeFile(string)" ) => 4054835277 )
      
    
    rule  ( selector ( "replace(string,string,string)" ) => 3758805054 )
      
    
    rule  ( selector ( "resetNonce(address)" ) => 477246573 )
      
    
    rule  ( selector ( "resumeGasMetering()" ) => 734875872 )
      
    
    rule  ( selector ( "revertTo(uint256)" ) => 1155002532 )
      
    
    rule  ( selector ( "revertToAndDelete(uint256)" ) => 65055913 )
      
    
    rule  ( selector ( "revokePersistent(address)" ) => 2574909986 )
      
    
    rule  ( selector ( "revokePersistent(address[])" ) => 1021929958 )
      
    
    rule  ( selector ( "roll(uint256)" ) => 528174896 )
      
    
    rule  ( selector ( "rollFork(bytes32)" ) => 254375723 )
      
    
    rule  ( selector ( "rollFork(uint256)" ) => 3652973473 )
      
    
    rule  ( selector ( "rollFork(uint256,bytes32)" ) => 4068675451 )
      
    
    rule  ( selector ( "rollFork(uint256,uint256)" ) => 3612115876 )
      
    
    rule  ( selector ( "rpc(string,string)" ) => 302434472 )
      
    
    rule  ( selector ( "rpc(string,string,string)" ) => 26845728 )
      
    
    rule  ( selector ( "rpcUrl(string)" ) => 2539285737 )
      
    
    rule  ( selector ( "rpcUrlStructs()" ) => 2636830506 )
      
    
    rule  ( selector ( "rpcUrls()" ) => 2824504344 )
      
    
    rule  ( selector ( "selectFork(uint256)" ) => 2663344167 )
      
    
    rule  ( selector ( "serializeAddress(string,string,address)" ) => 2536267874 )
      
    
    rule  ( selector ( "serializeAddress(string,string,address[])" ) => 506818074 )
      
    
    rule  ( selector ( "serializeBool(string,string,bool)" ) => 2887969137 )
      
    
    rule  ( selector ( "serializeBool(string,string,bool[])" ) => 2459064993 )
      
    
    rule  ( selector ( "serializeBytes(string,string,bytes)" ) => 4062008007 )
      
    
    rule  ( selector ( "serializeBytes(string,string,bytes[])" ) => 2558833202 )
      
    
    rule  ( selector ( "serializeBytes32(string,string,bytes32)" ) => 763439940 )
      
    
    rule  ( selector ( "serializeBytes32(string,string,bytes32[])" ) => 538854370 )
      
    
    rule  ( selector ( "serializeInt(string,string,int256)" ) => 1060363104 )
      
    
    rule  ( selector ( "serializeInt(string,string,int256[])" ) => 1987502375 )
      
    
    rule  ( selector ( "serializeJson(string,string)" ) => 2603833520 )
      
    
    rule  ( selector ( "serializeJsonType(string,bytes)" ) => 1833932454 )
      
    
    rule  ( selector ( "serializeJsonType(string,string,string,bytes)" ) => 1871953099 )
      
    
    rule  ( selector ( "serializeString(string,string,string)" ) => 2296016181 )
      
    
    rule  ( selector ( "serializeString(string,string,string[])" ) => 1444730611 )
      
    
    rule  ( selector ( "serializeUint(string,string,uint256)" ) => 312381442 )
      
    
    rule  ( selector ( "serializeUint(string,string,uint256[])" ) => 4276724841 )
      
    
    rule  ( selector ( "serializeUintToHex(string,string,uint256)" ) => 2925144808 )
      
    
    rule  ( selector ( "setBlockhash(uint256,bytes32)" ) => 1393866058 )
      
    
    rule  ( selector ( "setEnv(string,string)" ) => 1029252078 )
      
    
    rule  ( selector ( "setNonce(address,uint64)" ) => 4175530839 )
      
    
    rule  ( selector ( "setNonceUnsafe(address,uint64)" ) => 2607264284 )
      
    
    rule  ( selector ( "sign((address,uint256,uint256,uint256),bytes32)" ) => 2992396837 )
      
    
    rule  ( selector ( "sign(address,bytes32)" ) => 2350555653 )
      
    
    rule  ( selector ( "sign(bytes32)" ) => 2040320819 )
      
    
    rule  ( selector ( "sign(uint256,bytes32)" ) => 3812747940 )
      
    
    rule  ( selector ( "signCompact((address,uint256,uint256,uint256),bytes32)" ) => 1024338223 )
      
    
    rule  ( selector ( "signCompact(address,bytes32)" ) => 2385483711 )
      
    
    rule  ( selector ( "signCompact(bytes32)" ) => 2726485067 )
      
    
    rule  ( selector ( "signCompact(uint256,bytes32)" ) => 3425335327 )
      
    
    rule  ( selector ( "signP256(uint256,bytes32)" ) => 2199984960 )
      
    
    rule  ( selector ( "skip(bool)" ) => 3716337982 )
      
    
    rule  ( selector ( "sleep(uint256)" ) => 4204627731 )
      
    
    rule  ( selector ( "snapshot()" ) => 2534502746 )
      
    
    rule  ( selector ( "split(string,string)" ) => 2344047923 )
      
    
    rule  ( selector ( "startBroadcast()" ) => 2142579071 )
      
    
    rule  ( selector ( "startBroadcast(address)" ) => 2146183821 )
      
    
    rule  ( selector ( "startBroadcast(uint256)" ) => 3464592711 )
      
    
    rule  ( selector ( "startMappingRecording()" ) => 1050084800 )
      
    
    rule  ( selector ( "startPrank(address)" ) => 105151830 )
      
    
    rule  ( selector ( "startPrank(address,address)" ) => 1169514616 )
      
    
    rule  ( selector ( "startStateDiffRecording()" ) => 3475170249 )
      
    
    rule  ( selector ( "stopAndReturnStateDiff()" ) => 2858219790 )
      
    
    rule  ( selector ( "stopBroadcast()" ) => 1995103542 )
      
    
    rule  ( selector ( "stopExpectSafeMemory()" ) => 156648475 )
      
    
    rule  ( selector ( "stopMappingRecording()" ) => 222998171 )
      
    
    rule  ( selector ( "stopPrank()" ) => 2428830011 )
      
    
    rule  ( selector ( "store(address,bytes32,bytes32)" ) => 1892290747 )
      
    
    rule  ( selector ( "toBase64(bytes)" ) => 2781609573 )
      
    
    rule  ( selector ( "toBase64(string)" ) => 1066132168 )
      
    
    rule  ( selector ( "toBase64URL(bytes)" ) => 3367833162 )
      
    
    rule  ( selector ( "toBase64URL(string)" ) => 2922472883 )
      
    
    rule  ( selector ( "toLowercase(string)" ) => 1354434692 )
      
    
    rule  ( selector ( "toString(address)" ) => 1456103998 )
      
    
    rule  ( selector ( "toString(bool)" ) => 1910302682 )
      
    
    rule  ( selector ( "toString(bytes)" ) => 1907020045 )
      
    
    rule  ( selector ( "toString(bytes32)" ) => 2971277800 )
      
    
    rule  ( selector ( "toString(int256)" ) => 2736964622 )
      
    
    rule  ( selector ( "toString(uint256)" ) => 1761649582 )
      
    
    rule  ( selector ( "toUppercase(string)" ) => 122348503 )
      
    
    rule  ( selector ( "transact(bytes32)" ) => 3194252705 )
      
    
    rule  ( selector ( "transact(uint256,bytes32)" ) => 1300937803 )
      
    
    rule  ( selector ( "trim(string)" ) => 3000684885 )
      
    
    rule  ( selector ( "tryFfi(string[])" ) => 4099677415 )
      
    
    rule  ( selector ( "txGasPrice(uint256)" ) => 1224018959 )
      
    
    rule  ( selector ( "unixTime()" ) => 1649641436 )
      
    
    rule  ( selector ( "warp(uint256)" ) => 3856056066 )
      
    
    rule  ( selector ( "writeFile(string,string)" ) => 2306738839 )
      
    
    rule  ( selector ( "writeFileBinary(string,bytes)" ) => 522321024 )
      
    
    rule  ( selector ( "writeJson(string,string)" ) => 3795636639 )
      
    
    rule  ( selector ( "writeJson(string,string,string)" ) => 903261510 )
      
    
    rule  ( selector ( "writeLine(string,string)" ) => 1637714303 )
      
    
    rule  ( selector ( "writeToml(string,string)" ) => 3230030759 )
      
    
    rule  ( selector ( "writeToml(string,string,string)" ) => 1370253875 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModVmSafe-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModVmSafeContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeContract ::= "S2KlibZModforgeZSubstdZModsrcZModVmSafe" [symbol("contract_lib%forge-std%src%VmSafe")]
    
    syntax Bytes ::= S2KlibZModforgeZSubstdZModsrcZModVmSafeContract "." S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod [function, symbol("method_lib%forge-std%src%VmSafe")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kaccesses" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kaccesses_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kaddr" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kaddr_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbs_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbs_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbs_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbs" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbs_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbsDecimal_int256_int256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbsDecimal_int256_int256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbsDecimal_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqAbsDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqAbsDecimal_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRel" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRel_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRel" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRel_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRel" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRel_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRel" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRel_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRelDecimal_int256_int256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRelDecimal_int256_int256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRelDecimal_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertApproxEqRelDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertApproxEqRelDecimal_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_address_address_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_address_address_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bool_bool_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bool_bool_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes32_bytes32_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes32_bytes32_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes_bytes_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_bytes_bytes_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_int256_int256_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_int256_int256_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_string_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEq_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEqDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEqDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEqDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertEqDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertFalse" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertFalse_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertFalse" "(" Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertFalse_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGe" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGe_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGe" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGe_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGe" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGe_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGe" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGe_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGeDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGeDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGeDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGeDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGt" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGt_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGt" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGt_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGt" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGt_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGt" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGt_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGtDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGtDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGtDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertGtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertGtDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLe" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLe_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLe" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLe_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLe" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLe_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLe" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLe_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLeDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLeDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLeDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLeDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLeDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLeDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLt" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLt_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLt" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLt_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLt" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLt_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLt" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLt_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLtDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLtDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLtDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLtDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertLtDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertLtDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_address_address_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_address_address_address_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bool_bool_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bool_bool_bool_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes32_bytes32_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "bytes32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes32_bytes32_bytes32_bytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes_bytes_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," Bytes ":" "bytes" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_bytes_bytes_bytes_bytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_int256_int256_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," Int ":" "int256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_int256_int256_int256_int256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_string_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_uint256_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEq" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEq_uint256_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEqDecimal_int256_int256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "int256" "," Int ":" "int256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEqDecimal_int256_int256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEqDecimal_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertNotEqDecimal" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertNotEqDecimal_uint256_uint256_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertTrue" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertTrue_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KassertTrue" "(" Int ":" "bool" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KassertTrue_bool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kassume" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kassume_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kbreakpoint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kbreakpoint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kbreakpoint" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kbreakpoint_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kbroadcast" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kbroadcast_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kbroadcast" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kbroadcast_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kbroadcast" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kbroadcast_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KbroadcastRawTransaction" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KbroadcastRawTransaction_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcloseFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcloseFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcomputeCreate2Address" "(" Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcomputeCreate2Address_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcomputeCreate2Address" "(" Int ":" "bytes32" "," Int ":" "bytes32" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcomputeCreate2Address_bytes32_bytes32_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcomputeCreateAddress" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcomputeCreateAddress_address_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcopyFile" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcopyFile_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcreateDir" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcreateDir_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcreateWallet" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcreateWallet_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcreateWallet" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcreateWallet_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KcreateWallet" "(" Int ":" "uint256" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KcreateWallet_uint256_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KdeployCode" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KdeployCode_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KdeployCode" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KdeployCode_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KderiveKey" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KderiveKey_string_string_uint32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KderiveKey" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KderiveKey_string_string_uint32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KderiveKey" "(" String ":" "string" "," Int ":" "uint32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KderiveKey_string_uint32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KderiveKey" "(" String ":" "string" "," Int ":" "uint32" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KderiveKey_string_uint32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KensNamehash" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KensNamehash_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvAddress" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvAddress_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvAddress" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvAddress_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvBool" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvBool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvBool" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvBool_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvBytes" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvBytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvBytes" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvBytes_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvBytes32" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvBytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvBytes32" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvBytes32_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvExists" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvExists_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvInt" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvInt_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvInt" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvInt_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_string_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvOr" "(" String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvOr_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvString" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvString_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvString" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvString_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KenvUint" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KenvUint_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KethZUndgetLogs" "(" Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "address" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KethZUndgetLogs_uint256_uint256_address_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kexists" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kexists_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kffi" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kffi_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KfsMetadata" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KfsMetadata_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetBlobBaseFee" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetBlobBaseFee_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetBlockNumber" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetBlockNumber_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetBlockTimestamp" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetBlockTimestamp_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetCode" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetCode_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetDeployedCode" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetDeployedCode_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetFoundryVersion" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetFoundryVersion_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetLabel" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetLabel_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetMappingKeyAndParentOf" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetMappingKeyAndParentOf_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetMappingLength" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetMappingLength_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetMappingSlotAt" "(" Int ":" "address" "," Int ":" "bytes32" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetMappingSlotAt_address_bytes32_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetNonce" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetNonce_address_uint256_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetNonce" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetNonce_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KgetRecordedLogs" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KgetRecordedLogs_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KindexOf" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KindexOf_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KisContext" "(" Int ":" "uint8" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KisContext_uint8")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KisDir" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KisDir_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KisFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KisFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KkeyExists" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KkeyExists_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KkeyExistsJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KkeyExistsJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KkeyExistsToml" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KkeyExistsToml_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Klabel" "(" Int ":" "address" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Klabel_address_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KlastCallGas" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KlastCallGas_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kload" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kload_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseAddress" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseAddress_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseBool" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseBool_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseBytes" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseBytes_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseBytes32" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseBytes32_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseInt" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseInt_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJson" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJson_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonAddress" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonAddress_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonAddressArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonAddressArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonBool" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonBool_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonBoolArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonBoolArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonBytes" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonBytes_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonBytes32" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonBytes32_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonBytes32Array" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonBytes32Array_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonBytesArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonBytesArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonInt" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonInt_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonIntArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonIntArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonKeys" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonKeys_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonString" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonString_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonStringArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonStringArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonType" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonType_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonType" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonType_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonTypeArray" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonTypeArray_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonUint" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonUint_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseJsonUintArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseJsonUintArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseToml" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseToml_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseToml" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseToml_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlAddress" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlAddress_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlAddressArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlAddressArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlBool" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlBool_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlBoolArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlBoolArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlBytes" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlBytes_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlBytes32" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlBytes32_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlBytes32Array" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlBytes32Array_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlBytesArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlBytesArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlInt" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlInt_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlIntArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlIntArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlKeys" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlKeys_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlString" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlString_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlStringArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlStringArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlUint" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlUint_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseTomlUintArray" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseTomlUintArray_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KparseUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KparseUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KpauseGasMetering" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KpauseGasMetering_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KprojectRoot" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KprojectRoot_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kprompt" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kprompt_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KpromptAddress" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KpromptAddress_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KpromptSecret" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KpromptSecret_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KpromptSecretUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KpromptSecretUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KpromptUint" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KpromptUint_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrandomAddress" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrandomAddress_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrandomUint" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrandomUint_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrandomUint" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrandomUint_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KreadDir" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KreadDir_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KreadDir" "(" String ":" "string" "," Int ":" "uint64" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KreadDir_string_uint64")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KreadDir" "(" String ":" "string" "," Int ":" "uint64" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KreadDir_string_uint64_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KreadFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KreadFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KreadFileBinary" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KreadFileBinary_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KreadLine" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KreadLine_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KreadLink" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KreadLink_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Krecord" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Krecord_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrecordLogs" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrecordLogs_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrememberKey" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrememberKey_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KremoveDir" "(" String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KremoveDir_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KremoveFile" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KremoveFile_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Kreplace" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Kreplace_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KresumeGasMetering" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KresumeGasMetering_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Krpc" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Krpc_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Krpc" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Krpc_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrpcUrl" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrpcUrl_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrpcUrlStructs" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrpcUrlStructs_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KrpcUrls" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KrpcUrls_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeAddress" "(" String ":" "string" "," String ":" "string" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeAddress_string_string_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeAddress" "(" String ":" "string" "," String ":" "string" "," Int ":" "address" "," Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeAddress_string_string_address_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeBool" "(" String ":" "string" "," String ":" "string" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeBool_string_string_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeBool" "(" String ":" "string" "," String ":" "string" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeBool_string_string_bool_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeBytes" "(" String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeBytes_string_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeBytes" "(" String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeBytes_string_string_bytes_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeBytes32" "(" String ":" "string" "," String ":" "string" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeBytes32_string_string_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeBytes32" "(" String ":" "string" "," String ":" "string" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeBytes32_string_string_bytes32_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeInt" "(" String ":" "string" "," String ":" "string" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeInt_string_string_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeInt" "(" String ":" "string" "," String ":" "string" "," Int ":" "int256" "," Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeInt_string_string_int256_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeJsonType" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeJsonType_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeJsonType" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeJsonType_string_string_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeString" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeString_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeString" "(" String ":" "string" "," String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeString_string_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeUint" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeUint_string_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeUint" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeUint_string_string_uint256_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KserializeUintToHex" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KserializeUintToHex_string_string_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KsetEnv" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KsetEnv_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Ksign" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Ksign_address_uint256_uint256_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Ksign" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Ksign_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Ksign" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Ksign_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Ksign" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Ksign_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KsignCompact" "(" Int ":" "address" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KsignCompact_address_uint256_uint256_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KsignCompact" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KsignCompact_address_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KsignCompact" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KsignCompact_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KsignCompact" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KsignCompact_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KsignP256" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KsignP256_uint256_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Ksleep" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Ksleep_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Ksplit" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Ksplit_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstartBroadcast" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstartBroadcast_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstartBroadcast" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstartBroadcast_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstartBroadcast" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstartBroadcast_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstartMappingRecording" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstartMappingRecording_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstartStateDiffRecording" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstartStateDiffRecording_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstopAndReturnStateDiff" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstopAndReturnStateDiff_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstopBroadcast" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstopBroadcast_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KstopMappingRecording" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KstopMappingRecording_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoBase64" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoBase64_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoBase64" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoBase64_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoBase64URL" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoBase64URL_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoBase64URL" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoBase64URL_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoLowercase" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoLowercase_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoString" "(" Int ":" "address" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoString_address")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoString" "(" Int ":" "bool" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoString_bool")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoString" "(" Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoString_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoString" "(" Int ":" "bytes32" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoString_bytes32")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoString" "(" Int ":" "int256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoString_int256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoString" "(" Int ":" "uint256" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoString_uint256")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtoUppercase" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtoUppercase_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2Ktrim" "(" String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2Ktrim_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KtryFfi" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KtryFfi_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KunixTime" "(" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KunixTime_")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KwriteFile" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KwriteFile_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KwriteFileBinary" "(" String ":" "string" "," Bytes ":" "bytes" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KwriteFileBinary_string_bytes")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KwriteJson" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KwriteJson_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KwriteJson" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KwriteJson_string_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KwriteLine" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KwriteLine_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KwriteToml" "(" String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KwriteToml_string_string")]
    
    syntax S2KlibZModforgeZSubstdZModsrcZModVmSafeMethod ::= "S2KwriteToml" "(" String ":" "string" "," String ":" "string" "," String ":" "string" ")" [symbol("method_lib%forge-std%src%VmSafe_S2KwriteToml_string_string_string")]
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kaccesses ( V0_target : address ) => #abiCallData ( "accesses" , ( #address ( V0_target ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_target )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kaddr ( V0_privateKey : uint256 ) => #abiCallData ( "addr" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbs ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 ) => #abiCallData ( "assertApproxEqAbs" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbs ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqAbs" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbs ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 ) => #abiCallData ( "assertApproxEqAbs" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbs ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqAbs" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbsDecimal ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbsDecimal ( V0_left : int256 , V1_right : int256 , V2_maxDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbsDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqAbsDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqAbsDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRel ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 ) => #abiCallData ( "assertApproxEqRel" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRel ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqRel" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRel ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 ) => #abiCallData ( "assertApproxEqRel" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRel ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 , V3_error : string ) => #abiCallData ( "assertApproxEqRel" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRelDecimal ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRelDecimal ( V0_left : int256 , V1_right : int256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRelDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertApproxEqRelDecimal ( V0_left : uint256 , V1_right : uint256 , V2_maxPercentDelta : uint256 , V3_decimals : uint256 , V4_error : string ) => #abiCallData ( "assertApproxEqRelDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_maxPercentDelta ) , ( #uint256 ( V3_decimals ) , ( #string ( V4_error ) , .TypedArgs ) ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_maxPercentDelta )
       andBool ( #rangeUInt ( 256 , V3_decimals )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : address , V1_right : address ) => #abiCallData ( "assertEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : address , V1_right : address , V2_error : string ) => #abiCallData ( "assertEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address ) => #abiCallData ( "assertEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : bool , V1_right : bool ) => #abiCallData ( "assertEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : bool , V1_right : bool , V2_error : string ) => #abiCallData ( "assertEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool ) => #abiCallData ( "assertEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : bytes , V1_right : bytes ) => #abiCallData ( "assertEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : bytes , V1_right : bytes , V2_error : string ) => #abiCallData ( "assertEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : bytes32 , V1_right : bytes32 ) => #abiCallData ( "assertEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : bytes32 , V1_right : bytes32 , V2_error : string ) => #abiCallData ( "assertEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 ) => #abiCallData ( "assertEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes ) => #abiCallData ( "assertEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 ) => #abiCallData ( "assertEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : string , V1_right : string ) => #abiCallData ( "assertEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : string , V1_right : string , V2_error : string ) => #abiCallData ( "assertEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string ) => #abiCallData ( "assertEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 ) => #abiCallData ( "assertEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 , V2_error : string ) => #abiCallData ( "assertEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertFalse ( V0_condition : bool ) => #abiCallData ( "assertFalse" , ( #bool ( V0_condition ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertFalse ( V0_condition : bool , V1_error : string ) => #abiCallData ( "assertFalse" , ( #bool ( V0_condition ) , ( #string ( V1_error ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGe ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertGe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGe ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertGe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGe ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertGe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGe ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertGe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertGeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertGeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGt ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertGt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGt ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertGt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGt ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertGt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGt ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertGt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertGtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertGtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertGtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertGtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLe ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertLe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLe ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertLe" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLe ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertLe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLe ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertLe" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertLeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLeDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLeDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertLeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLeDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLeDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLt ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertLt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLt ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertLt" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLt ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertLt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLt ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertLt" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertLtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLtDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLtDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertLtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertLtDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertLtDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : address , V1_right : address ) => #abiCallData ( "assertNotEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : address , V1_right : address , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #address ( V0_left ) , ( #address ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left )
       andBool ( #rangeAddress ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address ) => #abiCallData ( "assertNotEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : address , V0_left_1 : address , V1_right_0 : address , V1_right_1 : address , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #address ( V0_left_0 ) , 2 , ( #address ( V0_left_0 ) , ( #address ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #address ( V1_right_0 ) , 2 , ( #address ( V1_right_0 ) , ( #address ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_left_0 )
       andBool ( #rangeAddress ( V0_left_1 )
       andBool ( #rangeAddress ( V1_right_0 )
       andBool ( #rangeAddress ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : bool , V1_right : bool ) => #abiCallData ( "assertNotEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : bool , V1_right : bool , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #bool ( V0_left ) , ( #bool ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left )
       andBool ( #rangeBool ( V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool ) => #abiCallData ( "assertNotEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : bool , V0_left_1 : bool , V1_right_0 : bool , V1_right_1 : bool , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #bool ( V0_left_0 ) , 2 , ( #bool ( V0_left_0 ) , ( #bool ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bool ( V1_right_0 ) , 2 , ( #bool ( V1_right_0 ) , ( #bool ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V0_left_0 )
       andBool ( #rangeBool ( V0_left_1 )
       andBool ( #rangeBool ( V1_right_0 )
       andBool ( #rangeBool ( V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : bytes , V1_right : bytes ) => #abiCallData ( "assertNotEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : bytes , V1_right : bytes , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #bytes ( V0_left ) , ( #bytes ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : bytes32 , V1_right : bytes32 ) => #abiCallData ( "assertNotEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : bytes32 , V1_right : bytes32 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #bytes32 ( V0_left ) , ( #bytes32 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left )
       andBool ( #rangeBytes ( 32 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : bytes32 , V0_left_1 : bytes32 , V1_right_0 : bytes32 , V1_right_1 : bytes32 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes32 ( V0_left_0 ) , 2 , ( #bytes32 ( V0_left_0 ) , ( #bytes32 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes32 ( V1_right_0 ) , 2 , ( #bytes32 ( V1_right_0 ) , ( #bytes32 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_left_0 )
       andBool ( #rangeBytes ( 32 , V0_left_1 )
       andBool ( #rangeBytes ( 32 , V1_right_0 )
       andBool ( #rangeBytes ( 32 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : bytes , V0_left_1 : bytes , V1_right_0 : bytes , V1_right_1 : bytes , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #bytes ( V0_left_0 ) , 2 , ( #bytes ( V0_left_0 ) , ( #bytes ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #bytes ( V1_right_0 ) , 2 , ( #bytes ( V1_right_0 ) , ( #bytes ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V0_left_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V0_left_1 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V1_right_1 ) )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : int256 , V1_right : int256 ) => #abiCallData ( "assertNotEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : int256 , V1_right : int256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 ) => #abiCallData ( "assertNotEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : int256 , V0_left_1 : int256 , V1_right_0 : int256 , V1_right_1 : int256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #int256 ( V0_left_0 ) , 2 , ( #int256 ( V0_left_0 ) , ( #int256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #int256 ( V1_right_0 ) , 2 , ( #int256 ( V1_right_0 ) , ( #int256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left_0 )
       andBool ( #rangeSInt ( 256 , V0_left_1 )
       andBool ( #rangeSInt ( 256 , V1_right_0 )
       andBool ( #rangeSInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : string , V1_right : string ) => #abiCallData ( "assertNotEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : string , V1_right : string , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #string ( V0_left ) , ( #string ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string ) => #abiCallData ( "assertNotEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : string , V0_left_1 : string , V1_right_0 : string , V1_right_1 : string , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #string ( V0_left_0 ) , 2 , ( #string ( V0_left_0 ) , ( #string ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #string ( V1_right_0 ) , 2 , ( #string ( V1_right_0 ) , ( #string ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : uint256 , V1_right : uint256 ) => #abiCallData ( "assertNotEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left : uint256 , V1_right : uint256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 ) => #abiCallData ( "assertNotEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEq ( V0_left_0 : uint256 , V0_left_1 : uint256 , V1_right_0 : uint256 , V1_right_1 : uint256 , V2_error : string ) => #abiCallData ( "assertNotEq" , ( #array ( #uint256 ( V0_left_0 ) , 2 , ( #uint256 ( V0_left_0 ) , ( #uint256 ( V0_left_1 ) , .TypedArgs ) ) ) , ( #array ( #uint256 ( V1_right_0 ) , 2 , ( #uint256 ( V1_right_0 ) , ( #uint256 ( V1_right_1 ) , .TypedArgs ) ) ) , ( #string ( V2_error ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left_0 )
       andBool ( #rangeUInt ( 256 , V0_left_1 )
       andBool ( #rangeUInt ( 256 , V1_right_0 )
       andBool ( #rangeUInt ( 256 , V1_right_1 )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 ) => #abiCallData ( "assertNotEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEqDecimal ( V0_left : int256 , V1_right : int256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertNotEqDecimal" , ( #int256 ( V0_left ) , ( #int256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V0_left )
       andBool ( #rangeSInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 ) => #abiCallData ( "assertNotEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertNotEqDecimal ( V0_left : uint256 , V1_right : uint256 , V2_decimals : uint256 , V3_error : string ) => #abiCallData ( "assertNotEqDecimal" , ( #uint256 ( V0_left ) , ( #uint256 ( V1_right ) , ( #uint256 ( V2_decimals ) , ( #string ( V3_error ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_left )
       andBool ( #rangeUInt ( 256 , V1_right )
       andBool ( #rangeUInt ( 256 , V2_decimals )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertTrue ( V0_condition : bool ) => #abiCallData ( "assertTrue" , ( #bool ( V0_condition ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KassertTrue ( V0_condition : bool , V1_error : string ) => #abiCallData ( "assertTrue" , ( #bool ( V0_condition ) , ( #string ( V1_error ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kassume ( V0_condition : bool ) => #abiCallData ( "assume" , ( #bool ( V0_condition ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_condition )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kbreakpoint ( V0_char : string ) => #abiCallData ( "breakpoint" , ( #string ( V0_char ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kbreakpoint ( V0_char : string , V1_value : bool ) => #abiCallData ( "breakpoint" , ( #string ( V0_char ) , ( #bool ( V1_value ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kbroadcast ( ) => #abiCallData ( "broadcast" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kbroadcast ( V0_signer : address ) => #abiCallData ( "broadcast" , ( #address ( V0_signer ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_signer )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kbroadcast ( V0_privateKey : uint256 ) => #abiCallData ( "broadcast" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KbroadcastRawTransaction ( V0_data : bytes ) => #abiCallData ( "broadcastRawTransaction" , ( #bytes ( V0_data ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcloseFile ( V0_path : string ) => #abiCallData ( "closeFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcomputeCreate2Address ( V0_salt : bytes32 , V1_initCodeHash : bytes32 ) => #abiCallData ( "computeCreate2Address" , ( #bytes32 ( V0_salt ) , ( #bytes32 ( V1_initCodeHash ) , .TypedArgs ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_salt )
       andBool ( #rangeBytes ( 32 , V1_initCodeHash )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcomputeCreate2Address ( V0_salt : bytes32 , V1_initCodeHash : bytes32 , V2_deployer : address ) => #abiCallData ( "computeCreate2Address" , ( #bytes32 ( V0_salt ) , ( #bytes32 ( V1_initCodeHash ) , ( #address ( V2_deployer ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V0_salt )
       andBool ( #rangeBytes ( 32 , V1_initCodeHash )
       andBool ( #rangeAddress ( V2_deployer )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcomputeCreateAddress ( V0_deployer : address , V1_nonce : uint256 ) => #abiCallData ( "computeCreateAddress" , ( #address ( V0_deployer ) , ( #uint256 ( V1_nonce ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_deployer )
       andBool ( #rangeUInt ( 256 , V1_nonce )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcopyFile ( V0_from : string , V1_to : string ) => #abiCallData ( "copyFile" , ( #string ( V0_from ) , ( #string ( V1_to ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcreateDir ( V0_path : string , V1_recursive : bool ) => #abiCallData ( "createDir" , ( #string ( V0_path ) , ( #bool ( V1_recursive ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_recursive )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcreateWallet ( V0_walletLabel : string ) => #abiCallData ( "createWallet" , ( #string ( V0_walletLabel ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcreateWallet ( V0_privateKey : uint256 ) => #abiCallData ( "createWallet" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KcreateWallet ( V0_privateKey : uint256 , V1_walletLabel : string ) => #abiCallData ( "createWallet" , ( #uint256 ( V0_privateKey ) , ( #string ( V1_walletLabel ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KdeployCode ( V0_artifactPath : string ) => #abiCallData ( "deployCode" , ( #string ( V0_artifactPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KdeployCode ( V0_artifactPath : string , V1_constructorArgs : bytes ) => #abiCallData ( "deployCode" , ( #string ( V0_artifactPath ) , ( #bytes ( V1_constructorArgs ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_constructorArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KderiveKey ( V0_mnemonic : string , V1_derivationPath : string , V2_index : uint32 ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #string ( V1_derivationPath ) , ( #uint32 ( V2_index ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 32 , V2_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KderiveKey ( V0_mnemonic : string , V1_derivationPath : string , V2_index : uint32 , V3_language : string ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #string ( V1_derivationPath ) , ( #uint32 ( V2_index ) , ( #string ( V3_language ) , .TypedArgs ) ) ) ) ) )
       ensures #rangeUInt ( 32 , V2_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KderiveKey ( V0_mnemonic : string , V1_index : uint32 ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #uint32 ( V1_index ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 32 , V1_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KderiveKey ( V0_mnemonic : string , V1_index : uint32 , V2_language : string ) => #abiCallData ( "deriveKey" , ( #string ( V0_mnemonic ) , ( #uint32 ( V1_index ) , ( #string ( V2_language ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 32 , V1_index )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KensNamehash ( V0_name : string ) => #abiCallData ( "ensNamehash" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvAddress ( V0_name : string ) => #abiCallData ( "envAddress" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvAddress ( V0_name : string , V1_delim : string ) => #abiCallData ( "envAddress" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvBool ( V0_name : string ) => #abiCallData ( "envBool" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvBool ( V0_name : string , V1_delim : string ) => #abiCallData ( "envBool" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvBytes ( V0_name : string ) => #abiCallData ( "envBytes" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvBytes ( V0_name : string , V1_delim : string ) => #abiCallData ( "envBytes" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvBytes32 ( V0_name : string ) => #abiCallData ( "envBytes32" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvBytes32 ( V0_name : string , V1_delim : string ) => #abiCallData ( "envBytes32" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvExists ( V0_name : string ) => #abiCallData ( "envExists" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvInt ( V0_name : string ) => #abiCallData ( "envInt" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvInt ( V0_name : string , V1_delim : string ) => #abiCallData ( "envInt" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_defaultValue : address ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #address ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeAddress ( V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_defaultValue : bool ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #bool ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_defaultValue : bytes ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #bytes ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_defaultValue ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_defaultValue : bytes32 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #bytes32 ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeBytes ( 32 , V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_defaultValue : int256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #int256 ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeSInt ( 256 , V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_defaultValue : string ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_defaultValue ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : address , V2_defaultValue_1 : address ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #address ( V2_defaultValue_0 ) , 2 , ( #address ( V2_defaultValue_0 ) , ( #address ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V2_defaultValue_0 )
       andBool ( #rangeAddress ( V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : bool , V2_defaultValue_1 : bool ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #bool ( V2_defaultValue_0 ) , 2 , ( #bool ( V2_defaultValue_0 ) , ( #bool ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V2_defaultValue_0 )
       andBool ( #rangeBool ( V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : bytes32 , V2_defaultValue_1 : bytes32 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #bytes32 ( V2_defaultValue_0 ) , 2 , ( #bytes32 ( V2_defaultValue_0 ) , ( #bytes32 ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V2_defaultValue_0 )
       andBool ( #rangeBytes ( 32 , V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : bytes , V2_defaultValue_1 : bytes ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #bytes ( V2_defaultValue_0 ) , 2 , ( #bytes ( V2_defaultValue_0 ) , ( #bytes ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V2_defaultValue_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_defaultValue_1 ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : int256 , V2_defaultValue_1 : int256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #int256 ( V2_defaultValue_0 ) , 2 , ( #int256 ( V2_defaultValue_0 ) , ( #int256 ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V2_defaultValue_0 )
       andBool ( #rangeSInt ( 256 , V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : string , V2_defaultValue_1 : string ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #string ( V2_defaultValue_0 ) , 2 , ( #string ( V2_defaultValue_0 ) , ( #string ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_delim : string , V2_defaultValue_0 : uint256 , V2_defaultValue_1 : uint256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #string ( V1_delim ) , ( #array ( #uint256 ( V2_defaultValue_0 ) , 2 , ( #uint256 ( V2_defaultValue_0 ) , ( #uint256 ( V2_defaultValue_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V2_defaultValue_0 )
       andBool ( #rangeUInt ( 256 , V2_defaultValue_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvOr ( V0_name : string , V1_defaultValue : uint256 ) => #abiCallData ( "envOr" , ( #string ( V0_name ) , ( #uint256 ( V1_defaultValue ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 256 , V1_defaultValue )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvString ( V0_name : string ) => #abiCallData ( "envString" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvString ( V0_name : string , V1_delim : string ) => #abiCallData ( "envString" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvUint ( V0_name : string ) => #abiCallData ( "envUint" , ( #string ( V0_name ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KenvUint ( V0_name : string , V1_delim : string ) => #abiCallData ( "envUint" , ( #string ( V0_name ) , ( #string ( V1_delim ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KethZUndgetLogs ( V0_fromBlock : uint256 , V1_toBlock : uint256 , V2_target : address , V3_topics_0 : bytes32 , V3_topics_1 : bytes32 ) => #abiCallData ( "eth_getLogs" , ( #uint256 ( V0_fromBlock ) , ( #uint256 ( V1_toBlock ) , ( #address ( V2_target ) , ( #array ( #bytes32 ( V3_topics_0 ) , 2 , ( #bytes32 ( V3_topics_0 ) , ( #bytes32 ( V3_topics_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_fromBlock )
       andBool ( #rangeUInt ( 256 , V1_toBlock )
       andBool ( #rangeAddress ( V2_target )
       andBool ( #rangeBytes ( 32 , V3_topics_0 )
       andBool ( #rangeBytes ( 32 , V3_topics_1 )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kexists ( V0_path : string ) => #abiCallData ( "exists" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kffi ( V0_commandInput_0 : string , V0_commandInput_1 : string ) => #abiCallData ( "ffi" , ( #array ( #string ( V0_commandInput_0 ) , 2 , ( #string ( V0_commandInput_0 ) , ( #string ( V0_commandInput_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KfsMetadata ( V0_path : string ) => #abiCallData ( "fsMetadata" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetBlobBaseFee ( ) => #abiCallData ( "getBlobBaseFee" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetBlockNumber ( ) => #abiCallData ( "getBlockNumber" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetBlockTimestamp ( ) => #abiCallData ( "getBlockTimestamp" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetCode ( V0_artifactPath : string ) => #abiCallData ( "getCode" , ( #string ( V0_artifactPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetDeployedCode ( V0_artifactPath : string ) => #abiCallData ( "getDeployedCode" , ( #string ( V0_artifactPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetFoundryVersion ( ) => #abiCallData ( "getFoundryVersion" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetLabel ( V0_account : address ) => #abiCallData ( "getLabel" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetMappingKeyAndParentOf ( V0_target : address , V1_elementSlot : bytes32 ) => #abiCallData ( "getMappingKeyAndParentOf" , ( #address ( V0_target ) , ( #bytes32 ( V1_elementSlot ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_elementSlot )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetMappingLength ( V0_target : address , V1_mappingSlot : bytes32 ) => #abiCallData ( "getMappingLength" , ( #address ( V0_target ) , ( #bytes32 ( V1_mappingSlot ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_mappingSlot )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetMappingSlotAt ( V0_target : address , V1_mappingSlot : bytes32 , V2_idx : uint256 ) => #abiCallData ( "getMappingSlotAt" , ( #address ( V0_target ) , ( #bytes32 ( V1_mappingSlot ) , ( #uint256 ( V2_idx ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_mappingSlot )
       andBool ( #rangeUInt ( 256 , V2_idx )
               )))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetNonce ( V0_addr : address , V1_publicKeyX : uint256 , V2_publicKeyY : uint256 , V3_privateKey : uint256 ) => #abiCallData ( "getNonce" , ( #tuple ( ( #address ( V0_addr ) , ( #uint256 ( V1_publicKeyX ) , ( #uint256 ( V2_publicKeyY ) , ( #uint256 ( V3_privateKey ) , .TypedArgs ) ) ) ) ) , .TypedArgs ) ) )
       ensures ( #rangeAddress ( V0_addr )
       andBool ( #rangeUInt ( 256 , V1_publicKeyX )
       andBool ( #rangeUInt ( 256 , V2_publicKeyY )
       andBool ( #rangeUInt ( 256 , V3_privateKey )
               ))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetNonce ( V0_account : address ) => #abiCallData ( "getNonce" , ( #address ( V0_account ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KgetRecordedLogs ( ) => #abiCallData ( "getRecordedLogs" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KindexOf ( V0_input : string , V1_key : string ) => #abiCallData ( "indexOf" , ( #string ( V0_input ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KisContext ( V0_context : uint8 ) => #abiCallData ( "isContext" , ( #uint8 ( V0_context ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 8 , V0_context )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KisDir ( V0_path : string ) => #abiCallData ( "isDir" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KisFile ( V0_path : string ) => #abiCallData ( "isFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KkeyExists ( V0_json : string , V1_key : string ) => #abiCallData ( "keyExists" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KkeyExistsJson ( V0_json : string , V1_key : string ) => #abiCallData ( "keyExistsJson" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KkeyExistsToml ( V0_toml : string , V1_key : string ) => #abiCallData ( "keyExistsToml" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Klabel ( V0_account : address , V1_newLabel : string ) => #abiCallData ( "label" , ( #address ( V0_account ) , ( #string ( V1_newLabel ) , .TypedArgs ) ) ) )
       ensures #rangeAddress ( V0_account )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KlastCallGas ( ) => #abiCallData ( "lastCallGas" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kload ( V0_target : address , V1_slot : bytes32 ) => #abiCallData ( "load" , ( #address ( V0_target ) , ( #bytes32 ( V1_slot ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_target )
       andBool ( #rangeBytes ( 32 , V1_slot )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseAddress ( V0_stringifiedValue : string ) => #abiCallData ( "parseAddress" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseBool ( V0_stringifiedValue : string ) => #abiCallData ( "parseBool" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseBytes ( V0_stringifiedValue : string ) => #abiCallData ( "parseBytes" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseBytes32 ( V0_stringifiedValue : string ) => #abiCallData ( "parseBytes32" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseInt ( V0_stringifiedValue : string ) => #abiCallData ( "parseInt" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJson ( V0_json : string ) => #abiCallData ( "parseJson" , ( #string ( V0_json ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJson ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJson" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonAddress ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonAddress" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonAddressArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonAddressArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonBool ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBool" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonBoolArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBoolArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonBytes ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytes" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonBytes32 ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytes32" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonBytes32Array ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytes32Array" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonBytesArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonBytesArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonInt ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonInt" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonIntArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonIntArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonKeys ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonKeys" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonString ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonString" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonStringArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonStringArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonType ( V0_json : string , V1_typeDescription : string ) => #abiCallData ( "parseJsonType" , ( #string ( V0_json ) , ( #string ( V1_typeDescription ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonType ( V0_json : string , V1_key : string , V2_typeDescription : string ) => #abiCallData ( "parseJsonType" , ( #string ( V0_json ) , ( #string ( V1_key ) , ( #string ( V2_typeDescription ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonTypeArray ( V0_json : string , V1_key : string , V2_typeDescription : string ) => #abiCallData ( "parseJsonTypeArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , ( #string ( V2_typeDescription ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonUint ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonUint" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseJsonUintArray ( V0_json : string , V1_key : string ) => #abiCallData ( "parseJsonUintArray" , ( #string ( V0_json ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseToml ( V0_toml : string ) => #abiCallData ( "parseToml" , ( #string ( V0_toml ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseToml ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseToml" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlAddress ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlAddress" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlAddressArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlAddressArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlBool ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBool" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlBoolArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBoolArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlBytes ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytes" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlBytes32 ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytes32" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlBytes32Array ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytes32Array" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlBytesArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlBytesArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlInt ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlInt" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlIntArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlIntArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlKeys ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlKeys" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlString ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlString" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlStringArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlStringArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlUint ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlUint" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseTomlUintArray ( V0_toml : string , V1_key : string ) => #abiCallData ( "parseTomlUintArray" , ( #string ( V0_toml ) , ( #string ( V1_key ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KparseUint ( V0_stringifiedValue : string ) => #abiCallData ( "parseUint" , ( #string ( V0_stringifiedValue ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KpauseGasMetering ( ) => #abiCallData ( "pauseGasMetering" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KprojectRoot ( ) => #abiCallData ( "projectRoot" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kprompt ( V0_promptText : string ) => #abiCallData ( "prompt" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KpromptAddress ( V0_promptText : string ) => #abiCallData ( "promptAddress" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KpromptSecret ( V0_promptText : string ) => #abiCallData ( "promptSecret" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KpromptSecretUint ( V0_promptText : string ) => #abiCallData ( "promptSecretUint" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KpromptUint ( V0_promptText : string ) => #abiCallData ( "promptUint" , ( #string ( V0_promptText ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrandomAddress ( ) => #abiCallData ( "randomAddress" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrandomUint ( ) => #abiCallData ( "randomUint" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrandomUint ( V0_min : uint256 , V1_max : uint256 ) => #abiCallData ( "randomUint" , ( #uint256 ( V0_min ) , ( #uint256 ( V1_max ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_min )
       andBool ( #rangeUInt ( 256 , V1_max )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KreadDir ( V0_path : string ) => #abiCallData ( "readDir" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KreadDir ( V0_path : string , V1_maxDepth : uint64 ) => #abiCallData ( "readDir" , ( #string ( V0_path ) , ( #uint64 ( V1_maxDepth ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , V1_maxDepth )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KreadDir ( V0_path : string , V1_maxDepth : uint64 , V2_followLinks : bool ) => #abiCallData ( "readDir" , ( #string ( V0_path ) , ( #uint64 ( V1_maxDepth ) , ( #bool ( V2_followLinks ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , V1_maxDepth )
       andBool ( #rangeBool ( V2_followLinks )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KreadFile ( V0_path : string ) => #abiCallData ( "readFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KreadFileBinary ( V0_path : string ) => #abiCallData ( "readFileBinary" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KreadLine ( V0_path : string ) => #abiCallData ( "readLine" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KreadLink ( V0_linkPath : string ) => #abiCallData ( "readLink" , ( #string ( V0_linkPath ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Krecord ( ) => #abiCallData ( "record" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrecordLogs ( ) => #abiCallData ( "recordLogs" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrememberKey ( V0_privateKey : uint256 ) => #abiCallData ( "rememberKey" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KremoveDir ( V0_path : string , V1_recursive : bool ) => #abiCallData ( "removeDir" , ( #string ( V0_path ) , ( #bool ( V1_recursive ) , .TypedArgs ) ) ) )
       ensures #rangeBool ( V1_recursive )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KremoveFile ( V0_path : string ) => #abiCallData ( "removeFile" , ( #string ( V0_path ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Kreplace ( V0_input : string , V1_from : string , V2_to : string ) => #abiCallData ( "replace" , ( #string ( V0_input ) , ( #string ( V1_from ) , ( #string ( V2_to ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KresumeGasMetering ( ) => #abiCallData ( "resumeGasMetering" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Krpc ( V0_method : string , V1_params : string ) => #abiCallData ( "rpc" , ( #string ( V0_method ) , ( #string ( V1_params ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Krpc ( V0_urlOrAlias : string , V1_method : string , V2_params : string ) => #abiCallData ( "rpc" , ( #string ( V0_urlOrAlias ) , ( #string ( V1_method ) , ( #string ( V2_params ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrpcUrl ( V0_rpcAlias : string ) => #abiCallData ( "rpcUrl" , ( #string ( V0_rpcAlias ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrpcUrlStructs ( ) => #abiCallData ( "rpcUrlStructs" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KrpcUrls ( ) => #abiCallData ( "rpcUrls" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeAddress ( V0_objectKey : string , V1_valueKey : string , V2_value : address ) => #abiCallData ( "serializeAddress" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #address ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeAddress ( V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeAddress ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : address , V2_values_1 : address ) => #abiCallData ( "serializeAddress" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #address ( V2_values_0 ) , 2 , ( #address ( V2_values_0 ) , ( #address ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeAddress ( V2_values_0 )
       andBool ( #rangeAddress ( V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeBool ( V0_objectKey : string , V1_valueKey : string , V2_value : bool ) => #abiCallData ( "serializeBool" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #bool ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeBool ( V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeBool ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : bool , V2_values_1 : bool ) => #abiCallData ( "serializeBool" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #bool ( V2_values_0 ) , 2 , ( #bool ( V2_values_0 ) , ( #bool ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBool ( V2_values_0 )
       andBool ( #rangeBool ( V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeBytes ( V0_objectKey : string , V1_valueKey : string , V2_value : bytes ) => #abiCallData ( "serializeBytes" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #bytes ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V2_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeBytes ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : bytes , V2_values_1 : bytes ) => #abiCallData ( "serializeBytes" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #bytes ( V2_values_0 ) , 2 , ( #bytes ( V2_values_0 ) , ( #bytes ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 64 , lengthBytes ( V2_values_0 ) )
       andBool ( #rangeUInt ( 64 , lengthBytes ( V2_values_1 ) )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeBytes32 ( V0_objectKey : string , V1_valueKey : string , V2_value : bytes32 ) => #abiCallData ( "serializeBytes32" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #bytes32 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeBytes ( 32 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeBytes32 ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : bytes32 , V2_values_1 : bytes32 ) => #abiCallData ( "serializeBytes32" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #bytes32 ( V2_values_0 ) , 2 , ( #bytes32 ( V2_values_0 ) , ( #bytes32 ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeBytes ( 32 , V2_values_0 )
       andBool ( #rangeBytes ( 32 , V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeInt ( V0_objectKey : string , V1_valueKey : string , V2_value : int256 ) => #abiCallData ( "serializeInt" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #int256 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeSInt ( 256 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeInt ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : int256 , V2_values_1 : int256 ) => #abiCallData ( "serializeInt" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #int256 ( V2_values_0 ) , 2 , ( #int256 ( V2_values_0 ) , ( #int256 ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeSInt ( 256 , V2_values_0 )
       andBool ( #rangeSInt ( 256 , V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeJson ( V0_objectKey : string , V1_value : string ) => #abiCallData ( "serializeJson" , ( #string ( V0_objectKey ) , ( #string ( V1_value ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeJsonType ( V0_typeDescription : string , V1_value : bytes ) => #abiCallData ( "serializeJsonType" , ( #string ( V0_typeDescription ) , ( #bytes ( V1_value ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeJsonType ( V0_objectKey : string , V1_valueKey : string , V2_typeDescription : string , V3_value : bytes ) => #abiCallData ( "serializeJsonType" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #string ( V2_typeDescription ) , ( #bytes ( V3_value ) , .TypedArgs ) ) ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V3_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeString ( V0_objectKey : string , V1_valueKey : string , V2_value : string ) => #abiCallData ( "serializeString" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #string ( V2_value ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeString ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : string , V2_values_1 : string ) => #abiCallData ( "serializeString" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #string ( V2_values_0 ) , 2 , ( #string ( V2_values_0 ) , ( #string ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeUint ( V0_objectKey : string , V1_valueKey : string , V2_value : uint256 ) => #abiCallData ( "serializeUint" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #uint256 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 256 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeUint ( V0_objectKey : string , V1_valueKey : string , V2_values_0 : uint256 , V2_values_1 : uint256 ) => #abiCallData ( "serializeUint" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #array ( #uint256 ( V2_values_0 ) , 2 , ( #uint256 ( V2_values_0 ) , ( #uint256 ( V2_values_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) ) ) )
       ensures ( #rangeUInt ( 256 , V2_values_0 )
       andBool ( #rangeUInt ( 256 , V2_values_1 )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KserializeUintToHex ( V0_objectKey : string , V1_valueKey : string , V2_value : uint256 ) => #abiCallData ( "serializeUintToHex" , ( #string ( V0_objectKey ) , ( #string ( V1_valueKey ) , ( #uint256 ( V2_value ) , .TypedArgs ) ) ) ) )
       ensures #rangeUInt ( 256 , V2_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KsetEnv ( V0_name : string , V1_value : string ) => #abiCallData ( "setEnv" , ( #string ( V0_name ) , ( #string ( V1_value ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Ksign ( V0_addr : address , V1_publicKeyX : uint256 , V2_publicKeyY : uint256 , V3_privateKey : uint256 , V4_digest : bytes32 ) => #abiCallData ( "sign" , ( #tuple ( ( #address ( V0_addr ) , ( #uint256 ( V1_publicKeyX ) , ( #uint256 ( V2_publicKeyY ) , ( #uint256 ( V3_privateKey ) , .TypedArgs ) ) ) ) ) , ( #bytes32 ( V4_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_addr )
       andBool ( #rangeUInt ( 256 , V1_publicKeyX )
       andBool ( #rangeUInt ( 256 , V2_publicKeyY )
       andBool ( #rangeUInt ( 256 , V3_privateKey )
       andBool ( #rangeBytes ( 32 , V4_digest )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Ksign ( V0_signer : address , V1_digest : bytes32 ) => #abiCallData ( "sign" , ( #address ( V0_signer ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_signer )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Ksign ( V0_digest : bytes32 ) => #abiCallData ( "sign" , ( #bytes32 ( V0_digest ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_digest )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Ksign ( V0_privateKey : uint256 , V1_digest : bytes32 ) => #abiCallData ( "sign" , ( #uint256 ( V0_privateKey ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_privateKey )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KsignCompact ( V0_addr : address , V1_publicKeyX : uint256 , V2_publicKeyY : uint256 , V3_privateKey : uint256 , V4_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #tuple ( ( #address ( V0_addr ) , ( #uint256 ( V1_publicKeyX ) , ( #uint256 ( V2_publicKeyY ) , ( #uint256 ( V3_privateKey ) , .TypedArgs ) ) ) ) ) , ( #bytes32 ( V4_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_addr )
       andBool ( #rangeUInt ( 256 , V1_publicKeyX )
       andBool ( #rangeUInt ( 256 , V2_publicKeyY )
       andBool ( #rangeUInt ( 256 , V3_privateKey )
       andBool ( #rangeBytes ( 32 , V4_digest )
               )))))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KsignCompact ( V0_signer : address , V1_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #address ( V0_signer ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeAddress ( V0_signer )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KsignCompact ( V0_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #bytes32 ( V0_digest ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_digest )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KsignCompact ( V0_privateKey : uint256 , V1_digest : bytes32 ) => #abiCallData ( "signCompact" , ( #uint256 ( V0_privateKey ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_privateKey )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KsignP256 ( V0_privateKey : uint256 , V1_digest : bytes32 ) => #abiCallData ( "signP256" , ( #uint256 ( V0_privateKey ) , ( #bytes32 ( V1_digest ) , .TypedArgs ) ) ) )
       ensures ( #rangeUInt ( 256 , V0_privateKey )
       andBool ( #rangeBytes ( 32 , V1_digest )
               ))
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Ksleep ( V0_duration : uint256 ) => #abiCallData ( "sleep" , ( #uint256 ( V0_duration ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_duration )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Ksplit ( V0_input : string , V1_delimiter : string ) => #abiCallData ( "split" , ( #string ( V0_input ) , ( #string ( V1_delimiter ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstartBroadcast ( ) => #abiCallData ( "startBroadcast" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstartBroadcast ( V0_signer : address ) => #abiCallData ( "startBroadcast" , ( #address ( V0_signer ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_signer )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstartBroadcast ( V0_privateKey : uint256 ) => #abiCallData ( "startBroadcast" , ( #uint256 ( V0_privateKey ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_privateKey )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstartMappingRecording ( ) => #abiCallData ( "startMappingRecording" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstartStateDiffRecording ( ) => #abiCallData ( "startStateDiffRecording" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstopAndReturnStateDiff ( ) => #abiCallData ( "stopAndReturnStateDiff" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstopBroadcast ( ) => #abiCallData ( "stopBroadcast" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KstopMappingRecording ( ) => #abiCallData ( "stopMappingRecording" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoBase64 ( V0_data : bytes ) => #abiCallData ( "toBase64" , ( #bytes ( V0_data ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoBase64 ( V0_data : string ) => #abiCallData ( "toBase64" , ( #string ( V0_data ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoBase64URL ( V0_data : bytes ) => #abiCallData ( "toBase64URL" , ( #bytes ( V0_data ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoBase64URL ( V0_data : string ) => #abiCallData ( "toBase64URL" , ( #string ( V0_data ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoLowercase ( V0_input : string ) => #abiCallData ( "toLowercase" , ( #string ( V0_input ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoString ( V0_value : address ) => #abiCallData ( "toString" , ( #address ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeAddress ( V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoString ( V0_value : bool ) => #abiCallData ( "toString" , ( #bool ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeBool ( V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoString ( V0_value : bytes ) => #abiCallData ( "toString" , ( #bytes ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V0_value ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoString ( V0_value : bytes32 ) => #abiCallData ( "toString" , ( #bytes32 ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeBytes ( 32 , V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoString ( V0_value : int256 ) => #abiCallData ( "toString" , ( #int256 ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeSInt ( 256 , V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoString ( V0_value : uint256 ) => #abiCallData ( "toString" , ( #uint256 ( V0_value ) , .TypedArgs ) ) )
       ensures #rangeUInt ( 256 , V0_value )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtoUppercase ( V0_input : string ) => #abiCallData ( "toUppercase" , ( #string ( V0_input ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2Ktrim ( V0_input : string ) => #abiCallData ( "trim" , ( #string ( V0_input ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KtryFfi ( V0_commandInput_0 : string , V0_commandInput_1 : string ) => #abiCallData ( "tryFfi" , ( #array ( #string ( V0_commandInput_0 ) , 2 , ( #string ( V0_commandInput_0 ) , ( #string ( V0_commandInput_1 ) , .TypedArgs ) ) ) , .TypedArgs ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KunixTime ( ) => #abiCallData ( "unixTime" , .TypedArgs ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KwriteFile ( V0_path : string , V1_data : string ) => #abiCallData ( "writeFile" , ( #string ( V0_path ) , ( #string ( V1_data ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KwriteFileBinary ( V0_path : string , V1_data : bytes ) => #abiCallData ( "writeFileBinary" , ( #string ( V0_path ) , ( #bytes ( V1_data ) , .TypedArgs ) ) ) )
       ensures #rangeUInt ( 64 , lengthBytes ( V1_data ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KwriteJson ( V0_json : string , V1_path : string ) => #abiCallData ( "writeJson" , ( #string ( V0_json ) , ( #string ( V1_path ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KwriteJson ( V0_json : string , V1_path : string , V2_valueKey : string ) => #abiCallData ( "writeJson" , ( #string ( V0_json ) , ( #string ( V1_path ) , ( #string ( V2_valueKey ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KwriteLine ( V0_path : string , V1_data : string ) => #abiCallData ( "writeLine" , ( #string ( V0_path ) , ( #string ( V1_data ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KwriteToml ( V0_json : string , V1_path : string ) => #abiCallData ( "writeToml" , ( #string ( V0_json ) , ( #string ( V1_path ) , .TypedArgs ) ) ) )
      
    
    rule  ( S2KlibZModforgeZSubstdZModsrcZModVmSafe . S2KwriteToml ( V0_json : string , V1_path : string , V2_valueKey : string ) => #abiCallData ( "writeToml" , ( #string ( V0_json ) , ( #string ( V1_path ) , ( #string ( V2_valueKey ) , .TypedArgs ) ) ) ) )
      
    
    rule  ( selector ( "accesses(address)" ) => 1706857601 )
      
    
    rule  ( selector ( "addr(uint256)" ) => 4288775753 )
      
    
    rule  ( selector ( "assertApproxEqAbs(int256,int256,uint256)" ) => 604996509 )
      
    
    rule  ( selector ( "assertApproxEqAbs(int256,int256,uint256,string)" ) => 2190075425 )
      
    
    rule  ( selector ( "assertApproxEqAbs(uint256,uint256,uint256)" ) => 382863302 )
      
    
    rule  ( selector ( "assertApproxEqAbs(uint256,uint256,uint256,string)" ) => 4145066082 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(int256,int256,uint256,uint256)" ) => 1029425340 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(int256,int256,uint256,uint256,string)" ) => 1783654100 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(uint256,uint256,uint256,uint256)" ) => 73160142 )
      
    
    rule  ( selector ( "assertApproxEqAbsDecimal(uint256,uint256,uint256,uint256,string)" ) => 1614978738 )
      
    
    rule  ( selector ( "assertApproxEqRel(int256,int256,uint256)" ) => 4272083279 )
      
    
    rule  ( selector ( "assertApproxEqRel(int256,int256,uint256,string)" ) => 4012342642 )
      
    
    rule  ( selector ( "assertApproxEqRel(uint256,uint256,uint256)" ) => 2364694260 )
      
    
    rule  ( selector ( "assertApproxEqRel(uint256,uint256,uint256,string)" ) => 516652339 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(int256,int256,uint256,uint256)" ) => 2881429964 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(int256,int256,uint256,uint256,string)" ) => 4241232324 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(uint256,uint256,uint256,uint256)" ) => 569190775 )
      
    
    rule  ( selector ( "assertApproxEqRelDecimal(uint256,uint256,uint256,uint256,string)" ) => 2195114237 )
      
    
    rule  ( selector ( "assertEq(address,address)" ) => 1364419062 )
      
    
    rule  ( selector ( "assertEq(address,address,string)" ) => 791112145 )
      
    
    rule  ( selector ( "assertEq(address[],address[])" ) => 946383924 )
      
    
    rule  ( selector ( "assertEq(address[],address[],string)" ) => 1049719749 )
      
    
    rule  ( selector ( "assertEq(bool,bool)" ) => 4160631927 )
      
    
    rule  ( selector ( "assertEq(bool,bool,string)" ) => 1303486078 )
      
    
    rule  ( selector ( "assertEq(bool[],bool[])" ) => 1887303557 )
      
    
    rule  ( selector ( "assertEq(bool[],bool[],string)" ) => 3834285965 )
      
    
    rule  ( selector ( "assertEq(bytes,bytes)" ) => 2539800113 )
      
    
    rule  ( selector ( "assertEq(bytes,bytes,string)" ) => 3796888832 )
      
    
    rule  ( selector ( "assertEq(bytes32,bytes32)" ) => 2089076379 )
      
    
    rule  ( selector ( "assertEq(bytes32,bytes32,string)" ) => 3254394576 )
      
    
    rule  ( selector ( "assertEq(bytes32[],bytes32[])" ) => 214560388 )
      
    
    rule  ( selector ( "assertEq(bytes32[],bytes32[],string)" ) => 3762196855 )
      
    
    rule  ( selector ( "assertEq(bytes[],bytes[])" ) => 3858471754 )
      
    
    rule  ( selector ( "assertEq(bytes[],bytes[],string)" ) => 4094947510 )
      
    
    rule  ( selector ( "assertEq(int256,int256)" ) => 4269076571 )
      
    
    rule  ( selector ( "assertEq(int256,int256,string)" ) => 1900687123 )
      
    
    rule  ( selector ( "assertEq(int256[],int256[])" ) => 1896891308 )
      
    
    rule  ( selector ( "assertEq(int256[],int256[],string)" ) => 421468976 )
      
    
    rule  ( selector ( "assertEq(string,string)" ) => 4079016291 )
      
    
    rule  ( selector ( "assertEq(string,string,string)" ) => 922113752 )
      
    
    rule  ( selector ( "assertEq(string[],string[])" ) => 3474719900 )
      
    
    rule  ( selector ( "assertEq(string[],string[],string)" ) => 4025922173 )
      
    
    rule  ( selector ( "assertEq(uint256,uint256)" ) => 2552851540 )
      
    
    rule  ( selector ( "assertEq(uint256,uint256,string)" ) => 2293517445 )
      
    
    rule  ( selector ( "assertEq(uint256[],uint256[])" ) => 2539477522 )
      
    
    rule  ( selector ( "assertEq(uint256[],uint256[],string)" ) => 1561904954 )
      
    
    rule  ( selector ( "assertEqDecimal(int256,int256,uint256)" ) => 1208052740 )
      
    
    rule  ( selector ( "assertEqDecimal(int256,int256,uint256,string)" ) => 2121773253 )
      
    
    rule  ( selector ( "assertEqDecimal(uint256,uint256,uint256)" ) => 665812380 )
      
    
    rule  ( selector ( "assertEqDecimal(uint256,uint256,uint256,string)" ) => 3503013359 )
      
    
    rule  ( selector ( "assertFalse(bool)" ) => 2778212485 )
      
    
    rule  ( selector ( "assertFalse(bool,string)" ) => 2074101769 )
      
    
    rule  ( selector ( "assertGe(int256,int256)" ) => 170964849 )
      
    
    rule  ( selector ( "assertGe(int256,int256,string)" ) => 2822973661 )
      
    
    rule  ( selector ( "assertGe(uint256,uint256)" ) => 2832519641 )
      
    
    rule  ( selector ( "assertGe(uint256,uint256,string)" ) => 3797041856 )
      
    
    rule  ( selector ( "assertGeDecimal(int256,int256,uint256)" ) => 3693658353 )
      
    
    rule  ( selector ( "assertGeDecimal(int256,int256,uint256,string)" ) => 1576615067 )
      
    
    rule  ( selector ( "assertGeDecimal(uint256,uint256,uint256)" ) => 1025499274 )
      
    
    rule  ( selector ( "assertGeDecimal(uint256,uint256,uint256,string)" ) => 2348781875 )
      
    
    rule  ( selector ( "assertGt(int256,int256)" ) => 1513499973 )
      
    
    rule  ( selector ( "assertGt(int256,int256,string)" ) => 4174592923 )
      
    
    rule  ( selector ( "assertGt(uint256,uint256)" ) => 3674733778 )
      
    
    rule  ( selector ( "assertGt(uint256,uint256,string)" ) => 3651388626 )
      
    
    rule  ( selector ( "assertGtDecimal(int256,int256,uint256)" ) => 2019630862 )
      
    
    rule  ( selector ( "assertGtDecimal(int256,int256,uint256,string)" ) => 77973419 )
      
    
    rule  ( selector ( "assertGtDecimal(uint256,uint256,uint256)" ) => 3972867127 )
      
    
    rule  ( selector ( "assertGtDecimal(uint256,uint256,uint256,string)" ) => 1687460493 )
      
    
    rule  ( selector ( "assertLe(int256,int256)" ) => 2516391246 )
      
    
    rule  ( selector ( "assertLe(int256,int256,string)" ) => 1308518700 )
      
    
    rule  ( selector ( "assertLe(uint256,uint256)" ) => 2221339669 )
      
    
    rule  ( selector ( "assertLe(uint256,uint256,string)" ) => 3514649357 )
      
    
    rule  ( selector ( "assertLeDecimal(int256,int256,uint256)" ) => 298923594 )
      
    
    rule  ( selector ( "assertLeDecimal(int256,int256,uint256,string)" ) => 2858219400 )
      
    
    rule  ( selector ( "assertLeDecimal(uint256,uint256,uint256)" ) => 3271862967 )
      
    
    rule  ( selector ( "assertLeDecimal(uint256,uint256,uint256,string)" ) => 2146417632 )
      
    
    rule  ( selector ( "assertLt(int256,int256)" ) => 1049706624 )
      
    
    rule  ( selector ( "assertLt(int256,int256,string)" ) => 2683646435 )
      
    
    rule  ( selector ( "assertLt(uint256,uint256)" ) => 2972696581 )
      
    
    rule  ( selector ( "assertLt(uint256,uint256,string)" ) => 1708507445 )
      
    
    rule  ( selector ( "assertLtDecimal(int256,int256,uint256)" ) => 3689470091 )
      
    
    rule  ( selector ( "assertLtDecimal(int256,int256,uint256,string)" ) => 1089516768 )
      
    
    rule  ( selector ( "assertLtDecimal(uint256,uint256,uint256)" ) => 544682878 )
      
    
    rule  ( selector ( "assertLtDecimal(uint256,uint256,uint256,string)" ) => 2842873911 )
      
    
    rule  ( selector ( "assertNotEq(address,address)" ) => 2972587668 )
      
    
    rule  ( selector ( "assertNotEq(address,address,string)" ) => 2272634257 )
      
    
    rule  ( selector ( "assertNotEq(address[],address[])" ) => 1188082258 )
      
    
    rule  ( selector ( "assertNotEq(address[],address[],string)" ) => 1925701813 )
      
    
    rule  ( selector ( "assertNotEq(bool,bool)" ) => 594431334 )
      
    
    rule  ( selector ( "assertNotEq(bool,bool,string)" ) => 277979745 )
      
    
    rule  ( selector ( "assertNotEq(bool[],bool[])" ) => 678408170 )
      
    
    rule  ( selector ( "assertNotEq(bool[],bool[],string)" ) => 1657207291 )
      
    
    rule  ( selector ( "assertNotEq(bytes,bytes)" ) => 1022856744 )
      
    
    rule  ( selector ( "assertNotEq(bytes,bytes,string)" ) => 2500285454 )
      
    
    rule  ( selector ( "assertNotEq(bytes32,bytes32)" ) => 2307818492 )
      
    
    rule  ( selector ( "assertNotEq(bytes32,bytes32,string)" ) => 2989698897 )
      
    
    rule  ( selector ( "assertNotEq(bytes32[],bytes32[])" ) => 100919912 )
      
    
    rule  ( selector ( "assertNotEq(bytes32[],bytes32[],string)" ) => 3094569804 )
      
    
    rule  ( selector ( "assertNotEq(bytes[],bytes[])" ) => 3991719989 )
      
    
    rule  ( selector ( "assertNotEq(bytes[],bytes[],string)" ) => 499982184 )
      
    
    rule  ( selector ( "assertNotEq(int256,int256)" ) => 4106224867 )
      
    
    rule  ( selector ( "assertNotEq(int256,int256,string)" ) => 1193592249 )
      
    
    rule  ( selector ( "assertNotEq(int256[],int256[])" ) => 192083183 )
      
    
    rule  ( selector ( "assertNotEq(int256[],int256[],string)" ) => 3549917986 )
      
    
    rule  ( selector ( "assertNotEq(string,string)" ) => 1786918835 )
      
    
    rule  ( selector ( "assertNotEq(string,string,string)" ) => 2025705127 )
      
    
    rule  ( selector ( "assertNotEq(string[],string[])" ) => 3187330024 )
      
    
    rule  ( selector ( "assertNotEq(string[],string[],string)" ) => 3060893683 )
      
    
    rule  ( selector ( "assertNotEq(uint256,uint256)" ) => 3079705376 )
      
    
    rule  ( selector ( "assertNotEq(uint256,uint256,string)" ) => 2566503869 )
      
    
    rule  ( selector ( "assertNotEq(uint256[],uint256[])" ) => 1458740410 )
      
    
    rule  ( selector ( "assertNotEq(uint256[],uint256[],string)" ) => 2592062863 )
      
    
    rule  ( selector ( "assertNotEqDecimal(int256,int256,uint256)" ) => 350705280 )
      
    
    rule  ( selector ( "assertNotEqDecimal(int256,int256,uint256,string)" ) => 865378059 )
      
    
    rule  ( selector ( "assertNotEqDecimal(uint256,uint256,uint256)" ) => 1721695399 )
      
    
    rule  ( selector ( "assertNotEqDecimal(uint256,uint256,uint256,string)" ) => 4121253208 )
      
    
    rule  ( selector ( "assertTrue(bool)" ) => 211801473 )
      
    
    rule  ( selector ( "assertTrue(bool,string)" ) => 2739854339 )
      
    
    rule  ( selector ( "assume(bool)" ) => 1281615202 )
      
    
    rule  ( selector ( "breakpoint(string)" ) => 4028997266 )
      
    
    rule  ( selector ( "breakpoint(string,bool)" ) => 4157840013 )
      
    
    rule  ( selector ( "broadcast()" ) => 2949218368 )
      
    
    rule  ( selector ( "broadcast(address)" ) => 3868601563 )
      
    
    rule  ( selector ( "broadcast(uint256)" ) => 4135229019 )
      
    
    rule  ( selector ( "broadcastRawTransaction(bytes)" ) => 2349626080 )
      
    
    rule  ( selector ( "closeFile(string)" ) => 1220748319 )
      
    
    rule  ( selector ( "computeCreate2Address(bytes32,bytes32)" ) => 2299275323 )
      
    
    rule  ( selector ( "computeCreate2Address(bytes32,bytes32,address)" ) => 3542319722 )
      
    
    rule  ( selector ( "computeCreateAddress(address,uint256)" ) => 1952676474 )
      
    
    rule  ( selector ( "copyFile(string,string)" ) => 2773125080 )
      
    
    rule  ( selector ( "createDir(string,bool)" ) => 378234067 )
      
    
    rule  ( selector ( "createWallet(string)" ) => 1946481106 )
      
    
    rule  ( selector ( "createWallet(uint256)" ) => 2053594038 )
      
    
    rule  ( selector ( "createWallet(uint256,string)" ) => 3984348258 )
      
    
    rule  ( selector ( "deployCode(string)" ) => 2592286112 )
      
    
    rule  ( selector ( "deployCode(string,bytes)" ) => 701406686 )
      
    
    rule  ( selector ( "deriveKey(string,string,uint32)" ) => 1808477211 )
      
    
    rule  ( selector ( "deriveKey(string,string,uint32,string)" ) => 690174751 )
      
    
    rule  ( selector ( "deriveKey(string,uint32)" ) => 1646872971 )
      
    
    rule  ( selector ( "deriveKey(string,uint32,string)" ) => 851973997 )
      
    
    rule  ( selector ( "ensNamehash(string)" ) => 2352434277 )
      
    
    rule  ( selector ( "envAddress(string)" ) => 890066623 )
      
    
    rule  ( selector ( "envAddress(string,string)" ) => 2905717242 )
      
    
    rule  ( selector ( "envBool(string)" ) => 2127686781 )
      
    
    rule  ( selector ( "envBool(string,string)" ) => 2863521455 )
      
    
    rule  ( selector ( "envBytes(string)" ) => 1299951366 )
      
    
    rule  ( selector ( "envBytes(string,string)" ) => 3720504603 )
      
    
    rule  ( selector ( "envBytes32(string)" ) => 2543095874 )
      
    
    rule  ( selector ( "envBytes32(string,string)" ) => 1525821889 )
      
    
    rule  ( selector ( "envExists(string)" ) => 3464717817 )
      
    
    rule  ( selector ( "envInt(string)" ) => 2301234273 )
      
    
    rule  ( selector ( "envInt(string,string)" ) => 1108873552 )
      
    
    rule  ( selector ( "envOr(string,address)" ) => 1444930880 )
      
    
    rule  ( selector ( "envOr(string,bool)" ) => 1199043535 )
      
    
    rule  ( selector ( "envOr(string,bytes)" ) => 3018094341 )
      
    
    rule  ( selector ( "envOr(string,bytes32)" ) => 3030931602 )
      
    
    rule  ( selector ( "envOr(string,int256)" ) => 3150672190 )
      
    
    rule  ( selector ( "envOr(string,string)" ) => 3510989676 )
      
    
    rule  ( selector ( "envOr(string,string,address[])" ) => 3343818219 )
      
    
    rule  ( selector ( "envOr(string,string,bool[])" ) => 3951421499 )
      
    
    rule  ( selector ( "envOr(string,string,bytes32[])" ) => 578941799 )
      
    
    rule  ( selector ( "envOr(string,string,bytes[])" ) => 1690058340 )
      
    
    rule  ( selector ( "envOr(string,string,int256[])" ) => 1191237451 )
      
    
    rule  ( selector ( "envOr(string,string,string[])" ) => 2240943804 )
      
    
    rule  ( selector ( "envOr(string,string,uint256[])" ) => 1949402408 )
      
    
    rule  ( selector ( "envOr(string,uint256)" ) => 1586967695 )
      
    
    rule  ( selector ( "envString(string)" ) => 4168600345 )
      
    
    rule  ( selector ( "envString(string,string)" ) => 347089865 )
      
    
    rule  ( selector ( "envUint(string)" ) => 3247934751 )
      
    
    rule  ( selector ( "envUint(string,string)" ) => 4091461785 )
      
    
    rule  ( selector ( "eth_getLogs(uint256,uint256,address,bytes32[])" ) => 903951515 )
      
    
    rule  ( selector ( "exists(string)" ) => 639251006 )
      
    
    rule  ( selector ( "ffi(string[])" ) => 2299921511 )
      
    
    rule  ( selector ( "fsMetadata(string)" ) => 2939587080 )
      
    
    rule  ( selector ( "getBlobBaseFee()" ) => 527265527 )
      
    
    rule  ( selector ( "getBlockNumber()" ) => 1120645468 )
      
    
    rule  ( selector ( "getBlockTimestamp()" ) => 2037090745 )
      
    
    rule  ( selector ( "getCode(string)" ) => 2367473957 )
      
    
    rule  ( selector ( "getDeployedCode(string)" ) => 1052734388 )
      
    
    rule  ( selector ( "getFoundryVersion()" ) => 3935902645 )
      
    
    rule  ( selector ( "getLabel(address)" ) => 681724336 )
      
    
    rule  ( selector ( "getMappingKeyAndParentOf(address,bytes32)" ) => 2272142566 )
      
    
    rule  ( selector ( "getMappingLength(address,bytes32)" ) => 791664191 )
      
    
    rule  ( selector ( "getMappingSlotAt(address,bytes32,uint256)" ) => 3955702452 )
      
    
    rule  ( selector ( "getNonce((address,uint256,uint256,uint256))" ) => 2775878317 )
      
    
    rule  ( selector ( "getNonce(address)" ) => 755185067 )
      
    
    rule  ( selector ( "getRecordedLogs()" ) => 420828068 )
      
    
    rule  ( selector ( "indexOf(string,string)" ) => 2315782071 )
      
    
    rule  ( selector ( "isContext(uint8)" ) => 1689199965 )
      
    
    rule  ( selector ( "isDir(string)" ) => 2098581529 )
      
    
    rule  ( selector ( "isFile(string)" ) => 3773498580 )
      
    
    rule  ( selector ( "keyExists(string,string)" ) => 1384802364 )
      
    
    rule  ( selector ( "keyExistsJson(string,string)" ) => 3678549494 )
      
    
    rule  ( selector ( "keyExistsToml(string,string)" ) => 1611203501 )
      
    
    rule  ( selector ( "label(address,string)" ) => 3327641368 )
      
    
    rule  ( selector ( "lastCallGas()" ) => 727227176 )
      
    
    rule  ( selector ( "load(address,bytes32)" ) => 1719639408 )
      
    
    rule  ( selector ( "parseAddress(string)" ) => 3335390621 )
      
    
    rule  ( selector ( "parseBool(string)" ) => 2538535204 )
      
    
    rule  ( selector ( "parseBytes(string)" ) => 2405245741 )
      
    
    rule  ( selector ( "parseBytes32(string)" ) => 142503553 )
      
    
    rule  ( selector ( "parseInt(string)" ) => 1110731870 )
      
    
    rule  ( selector ( "parseJson(string)" ) => 1786929162 )
      
    
    rule  ( selector ( "parseJson(string,string)" ) => 2241072881 )
      
    
    rule  ( selector ( "parseJsonAddress(string,string)" ) => 505013847 )
      
    
    rule  ( selector ( "parseJsonAddressArray(string,string)" ) => 802060419 )
      
    
    rule  ( selector ( "parseJsonBool(string,string)" ) => 2676415633 )
      
    
    rule  ( selector ( "parseJsonBoolArray(string,string)" ) => 2448669007 )
      
    
    rule  ( selector ( "parseJsonBytes(string,string)" ) => 4254211048 )
      
    
    rule  ( selector ( "parseJsonBytes32(string,string)" ) => 393733533 )
      
    
    rule  ( selector ( "parseJsonBytes32Array(string,string)" ) => 2445761475 )
      
    
    rule  ( selector ( "parseJsonBytesArray(string,string)" ) => 1714530969 )
      
    
    rule  ( selector ( "parseJsonInt(string,string)" ) => 2063895757 )
      
    
    rule  ( selector ( "parseJsonIntArray(string,string)" ) => 2575549066 )
      
    
    rule  ( selector ( "parseJsonKeys(string,string)" ) => 557728152 )
      
    
    rule  ( selector ( "parseJsonString(string,string)" ) => 1237646024 )
      
    
    rule  ( selector ( "parseJsonStringArray(string,string)" ) => 1234164980 )
      
    
    rule  ( selector ( "parseJsonType(string,string)" ) => 2849648955 )
      
    
    rule  ( selector ( "parseJsonType(string,string,string)" ) => 3824528947 )
      
    
    rule  ( selector ( "parseJsonTypeArray(string,string,string)" ) => 24499509 )
      
    
    rule  ( selector ( "parseJsonUint(string,string)" ) => 2916999862 )
      
    
    rule  ( selector ( "parseJsonUintArray(string,string)" ) => 1377858731 )
      
    
    rule  ( selector ( "parseToml(string)" ) => 1495355888 )
      
    
    rule  ( selector ( "parseToml(string,string)" ) => 930311688 )
      
    
    rule  ( selector ( "parseTomlAddress(string,string)" ) => 1709688900 )
      
    
    rule  ( selector ( "parseTomlAddressArray(string,string)" ) => 1707354343 )
      
    
    rule  ( selector ( "parseTomlBool(string,string)" ) => 3540897494 )
      
    
    rule  ( selector ( "parseTomlBoolArray(string,string)" ) => 310181530 )
      
    
    rule  ( selector ( "parseTomlBytes(string,string)" ) => 3615227321 )
      
    
    rule  ( selector ( "parseTomlBytes32(string,string)" ) => 2384545808 )
      
    
    rule  ( selector ( "parseTomlBytes32Array(string,string)" ) => 1047621505 )
      
    
    rule  ( selector ( "parseTomlBytesArray(string,string)" ) => 2979512903 )
      
    
    rule  ( selector ( "parseTomlInt(string,string)" ) => 3241477945 )
      
    
    rule  ( selector ( "parseTomlIntArray(string,string)" ) => 3545377510 )
      
    
    rule  ( selector ( "parseTomlKeys(string,string)" ) => 2167030962 )
      
    
    rule  ( selector ( "parseTomlString(string,string)" ) => 2344148291 )
      
    
    rule  ( selector ( "parseTomlStringArray(string,string)" ) => 2674037377 )
      
    
    rule  ( selector ( "parseTomlUint(string,string)" ) => 3430614151 )
      
    
    rule  ( selector ( "parseTomlUintArray(string,string)" ) => 3051300808 )
      
    
    rule  ( selector ( "parseUint(string)" ) => 4203824461 )
      
    
    rule  ( selector ( "pauseGasMetering()" ) => 3517297519 )
      
    
    rule  ( selector ( "projectRoot()" ) => 3643842790 )
      
    
    rule  ( selector ( "prompt(string)" ) => 1206580340 )
      
    
    rule  ( selector ( "promptAddress(string)" ) => 1659766260 )
      
    
    rule  ( selector ( "promptSecret(string)" ) => 505912641 )
      
    
    rule  ( selector ( "promptSecretUint(string)" ) => 1774846647 )
      
    
    rule  ( selector ( "promptUint(string)" ) => 1697633417 )
      
    
    rule  ( selector ( "randomAddress()" ) => 3586058741 )
      
    
    rule  ( selector ( "randomUint()" ) => 621954864 )
      
    
    rule  ( selector ( "randomUint(uint256,uint256)" ) => 3592095003 )
      
    
    rule  ( selector ( "readDir(string)" ) => 3300678112 )
      
    
    rule  ( selector ( "readDir(string,uint64)" ) => 345474924 )
      
    
    rule  ( selector ( "readDir(string,uint64,bool)" ) => 2164446989 )
      
    
    rule  ( selector ( "readFile(string)" ) => 1626979089 )
      
    
    rule  ( selector ( "readFileBinary(string)" ) => 384662468 )
      
    
    rule  ( selector ( "readLine(string)" ) => 1895126824 )
      
    
    rule  ( selector ( "readLink(string)" ) => 2673247394 )
      
    
    rule  ( selector ( "record()" ) => 644673801 )
      
    
    rule  ( selector ( "recordLogs()" ) => 1101999954 )
      
    
    rule  ( selector ( "rememberKey(uint256)" ) => 571474020 )
      
    
    rule  ( selector ( "removeDir(string,bool)" ) => 1170612241 )
      
    
    rule  ( selector ( "removeFile(string)" ) => 4054835277 )
      
    
    rule  ( selector ( "replace(string,string,string)" ) => 3758805054 )
      
    
    rule  ( selector ( "resumeGasMetering()" ) => 734875872 )
      
    
    rule  ( selector ( "rpc(string,string)" ) => 302434472 )
      
    
    rule  ( selector ( "rpc(string,string,string)" ) => 26845728 )
      
    
    rule  ( selector ( "rpcUrl(string)" ) => 2539285737 )
      
    
    rule  ( selector ( "rpcUrlStructs()" ) => 2636830506 )
      
    
    rule  ( selector ( "rpcUrls()" ) => 2824504344 )
      
    
    rule  ( selector ( "serializeAddress(string,string,address)" ) => 2536267874 )
      
    
    rule  ( selector ( "serializeAddress(string,string,address[])" ) => 506818074 )
      
    
    rule  ( selector ( "serializeBool(string,string,bool)" ) => 2887969137 )
      
    
    rule  ( selector ( "serializeBool(string,string,bool[])" ) => 2459064993 )
      
    
    rule  ( selector ( "serializeBytes(string,string,bytes)" ) => 4062008007 )
      
    
    rule  ( selector ( "serializeBytes(string,string,bytes[])" ) => 2558833202 )
      
    
    rule  ( selector ( "serializeBytes32(string,string,bytes32)" ) => 763439940 )
      
    
    rule  ( selector ( "serializeBytes32(string,string,bytes32[])" ) => 538854370 )
      
    
    rule  ( selector ( "serializeInt(string,string,int256)" ) => 1060363104 )
      
    
    rule  ( selector ( "serializeInt(string,string,int256[])" ) => 1987502375 )
      
    
    rule  ( selector ( "serializeJson(string,string)" ) => 2603833520 )
      
    
    rule  ( selector ( "serializeJsonType(string,bytes)" ) => 1833932454 )
      
    
    rule  ( selector ( "serializeJsonType(string,string,string,bytes)" ) => 1871953099 )
      
    
    rule  ( selector ( "serializeString(string,string,string)" ) => 2296016181 )
      
    
    rule  ( selector ( "serializeString(string,string,string[])" ) => 1444730611 )
      
    
    rule  ( selector ( "serializeUint(string,string,uint256)" ) => 312381442 )
      
    
    rule  ( selector ( "serializeUint(string,string,uint256[])" ) => 4276724841 )
      
    
    rule  ( selector ( "serializeUintToHex(string,string,uint256)" ) => 2925144808 )
      
    
    rule  ( selector ( "setEnv(string,string)" ) => 1029252078 )
      
    
    rule  ( selector ( "sign((address,uint256,uint256,uint256),bytes32)" ) => 2992396837 )
      
    
    rule  ( selector ( "sign(address,bytes32)" ) => 2350555653 )
      
    
    rule  ( selector ( "sign(bytes32)" ) => 2040320819 )
      
    
    rule  ( selector ( "sign(uint256,bytes32)" ) => 3812747940 )
      
    
    rule  ( selector ( "signCompact((address,uint256,uint256,uint256),bytes32)" ) => 1024338223 )
      
    
    rule  ( selector ( "signCompact(address,bytes32)" ) => 2385483711 )
      
    
    rule  ( selector ( "signCompact(bytes32)" ) => 2726485067 )
      
    
    rule  ( selector ( "signCompact(uint256,bytes32)" ) => 3425335327 )
      
    
    rule  ( selector ( "signP256(uint256,bytes32)" ) => 2199984960 )
      
    
    rule  ( selector ( "sleep(uint256)" ) => 4204627731 )
      
    
    rule  ( selector ( "split(string,string)" ) => 2344047923 )
      
    
    rule  ( selector ( "startBroadcast()" ) => 2142579071 )
      
    
    rule  ( selector ( "startBroadcast(address)" ) => 2146183821 )
      
    
    rule  ( selector ( "startBroadcast(uint256)" ) => 3464592711 )
      
    
    rule  ( selector ( "startMappingRecording()" ) => 1050084800 )
      
    
    rule  ( selector ( "startStateDiffRecording()" ) => 3475170249 )
      
    
    rule  ( selector ( "stopAndReturnStateDiff()" ) => 2858219790 )
      
    
    rule  ( selector ( "stopBroadcast()" ) => 1995103542 )
      
    
    rule  ( selector ( "stopMappingRecording()" ) => 222998171 )
      
    
    rule  ( selector ( "toBase64(bytes)" ) => 2781609573 )
      
    
    rule  ( selector ( "toBase64(string)" ) => 1066132168 )
      
    
    rule  ( selector ( "toBase64URL(bytes)" ) => 3367833162 )
      
    
    rule  ( selector ( "toBase64URL(string)" ) => 2922472883 )
      
    
    rule  ( selector ( "toLowercase(string)" ) => 1354434692 )
      
    
    rule  ( selector ( "toString(address)" ) => 1456103998 )
      
    
    rule  ( selector ( "toString(bool)" ) => 1910302682 )
      
    
    rule  ( selector ( "toString(bytes)" ) => 1907020045 )
      
    
    rule  ( selector ( "toString(bytes32)" ) => 2971277800 )
      
    
    rule  ( selector ( "toString(int256)" ) => 2736964622 )
      
    
    rule  ( selector ( "toString(uint256)" ) => 1761649582 )
      
    
    rule  ( selector ( "toUppercase(string)" ) => 122348503 )
      
    
    rule  ( selector ( "trim(string)" ) => 3000684885 )
      
    
    rule  ( selector ( "tryFfi(string[])" ) => 4099677415 )
      
    
    rule  ( selector ( "unixTime()" ) => 1649641436 )
      
    
    rule  ( selector ( "writeFile(string,string)" ) => 2306738839 )
      
    
    rule  ( selector ( "writeFileBinary(string,bytes)" ) => 522321024 )
      
    
    rule  ( selector ( "writeJson(string,string)" ) => 3795636639 )
      
    
    rule  ( selector ( "writeJson(string,string,string)" ) => 903261510 )
      
    
    rule  ( selector ( "writeLine(string,string)" ) => 1637714303 )
      
    
    rule  ( selector ( "writeToml(string,string)" ) => 3230030759 )
      
    
    rule  ( selector ( "writeToml(string,string,string)" ) => 1370253875 )
      

endmodule

module S2KlibZModforgeZSubstdZModsrcZModconsole-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModconsoleContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModconsoleContract ::= "S2KlibZModforgeZSubstdZModsrcZModconsole" [symbol("contract_lib%forge-std%src%console")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModconsole2-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModconsole2Contract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModconsole2Contract ::= "S2KlibZModforgeZSubstdZModsrcZModconsole2" [symbol("contract_lib%forge-std%src%console2")]

endmodule

module S2KlibZModforgeZSubstdZModsrcZModsafeconsole-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= S2KlibZModforgeZSubstdZModsrcZModsafeconsoleContract
    
    syntax S2KlibZModforgeZSubstdZModsrcZModsafeconsoleContract ::= "S2KlibZModforgeZSubstdZModsrcZModsafeconsole" [symbol("contract_lib%forge-std%src%safeconsole")]

endmodule
