import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ Setup.class, Build.class, Initialize.class, Kompile.class, RunPrograms.class })
public class AllTests {

	@Test
	public void all()
	{
	}
}
