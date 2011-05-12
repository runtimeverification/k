kmod GRAPH-COLORING-CONFIG is including K + PL-INT + PL-STRING + PL-NAT
  syntax GraphType ::= gtCards | gtColors | gtcg | gtng
  syntax K ::= GraphType | servers( Nat ) | setup | start | run
  syntax K ::= Int | String | Nat

  configuration
    <top>
      <k>.K</k>
      <graphType>.K</graphType>
      <dependencies>.Set</dependencies>
      <cards>.Set</cards>
      <meta>.Bag</meta>
      <time>-1</time>
      <total-cost>0</total-cost>
      <graph>
        <g-edge multiplicity="*">
          <ge-name>.K</ge-name>
          <ge-from>.K</ge-from>
          <ge-to>.K</ge-to>
          <ge-color>.K</ge-color>
          <ge-length>0</ge-length>
          <ge-cards>.Set</ge-cards>
          <ge-dependencies>.Set</ge-dependencies>
        </g-edge>
      </graph>
      <network>
        <master>.K</master>
        <node multiplicity="*">
          <n-name>.K</n-name>
          <n-cards>.Set</n-cards>
          <n-server-names>.Set</n-server-names>
          <n-edges>
            <n-edge multiplicity="*">
              <ne-to>.K</ne-to>
              <ne-length>0</ne-length>
              <ne-cost>0</ne-cost>
              <ne-servers>
                <server>
                  <s-name>.K</s-name>
                  <s-cards>.Set</s-cards>
                  <s-length>0</s-length>
                </server>
              </ne-servers>
            </n-edge>
          </n-edges>
          <processors>
            <processor multiplicity="*">
              <p-name>.K</p-name>
              <p-color>.K</p-color>
            </processor>
          </processors>
        </node>
        <all-node-server-names>.Set</all-node-server-names>
        <all-edge-server-names>.Set</all-edge-server-names>
        <working-server-names>.Set</working-server-names>
        <all-node-processor-names>.Set</all-node-processor-names>
        <working-processor-names>.Set</working-processor-names>
      </network>
    </top>
endkm
