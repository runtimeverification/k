package ro.uaic.fmse.kplugin.navigation;

import com.intellij.navigation.ChooseByNameContributor;
import com.intellij.navigation.NavigationItem;
import com.intellij.openapi.project.Project;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.psi.KPsiUtil;
import ro.uaic.fmse.kplugin.psi.KRegularProduction;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Denis Bogdanas
 *         Created on 12/18/13.
 */
public class KChooseByNameContributor implements ChooseByNameContributor {
    @NotNull
    @Override
    public String[] getNames(Project project, boolean includeNonProjectItems) {
        List<KRegularProduction> syntaxDefs = KPsiUtil.findSyntaxDefs(project);
        List<String> names = new ArrayList<>(syntaxDefs.size());
        for (KRegularProduction syntaxDef : syntaxDefs) {
            if (syntaxDef.getName() != null && syntaxDef.getName().length() > 0) {
                names.add(syntaxDef.getName());
            }
        }
        return names.toArray(new String[names.size()]);
    }

    @NotNull
    @Override
    public NavigationItem[] getItemsByName(String name, String pattern, Project project,
                                           boolean includeNonProjectItems) {
        List<KRegularProduction> syntaxDefs = KPsiUtil.findSyntaxDefs(project, name);
        //noinspection SuspiciousToArrayCall
        return syntaxDefs.toArray(new NavigationItem[syntaxDefs.size()]);
    }
}
