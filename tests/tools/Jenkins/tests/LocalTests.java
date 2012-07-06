import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;


@RunWith(Suite.class)
@SuiteClasses({ InitLocal.class, Initialize.class, Kompile.class, RunPrograms.class 
		})
public class LocalTests {

}
