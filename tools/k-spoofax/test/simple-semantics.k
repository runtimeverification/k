kmod SIMPLE-UNTYPED-SEMANTICS is
	configuration
	<T color="red">
		<threads color="orange">
			<thread multiplicity="*" color="yellow">
			<k color="green"> .K </k>
			<fstack color="blue"> .List </fstack>
			<xstack color="purple"> .List </xstack>
			<env color="violet"> .Map </env>
			<holds color="black"> .Map </holds>
			</thread>
		</threads>
		<genv color="pink"> .Map </genv>
		<store color="white"> .Map </store>
		<busy color="cyan"> .Set </busy>
		<in color="magenta"> .List </in>
		<out color="brown"> .List </out>
		<nextLoc color="gray"> 0 </nextLoc>
	</T>
	
	rule I1 * I2 => '*Int(I1, I2)
endkm