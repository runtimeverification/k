/**
 * 
 */
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class TagFactory {

	public static Tag createTag(Element element, Map<String, String> consMap) {
		
		
	if (Constants.MODULE_module_TAG.equals(element.getNodeName()))
		return new MODULE_module_TAG(element, consMap);
	if (Constants.IMPORTS_imports_TAG.equals(element.getNodeName()))
		return new IMPORTS_imports_TAG(element, consMap);
	if (Constants.MODULEIMPORT_moduleImport_TAG.equals(element.getNodeName()))
		return new MODULEIMPORT_moduleImport_TAG(element, consMap);
	if (Constants.SYNTAX_syntax_TAG.equals(element.getNodeName()))
		return new SYNTAX_syntax_TAG(element, consMap);
	if (Constants.SORT_sort_TAG.equals(element.getNodeName()))
		return new SORT_sort_TAG(element, consMap);
	if (Constants.PRIORITY_priority_TAG.equals(element.getNodeName()))
		return new PRIORITY_priority_TAG(element, consMap);
	if (Constants.PRODUCTION_production_TAG.equals(element.getNodeName()))
		return new PRODUCTION_production_TAG(element, consMap);
	if (Constants.TERMINAL_terminal_TAG.equals(element.getNodeName()))
		return new TERMINAL_terminal_TAG(element, consMap);
	if (Constants.ANNOS_annos_TAG.equals(element.getNodeName()))
		return new ANNOS_annos_TAG(element, consMap);
	if (Constants.TAG_tag_TAG.equals(element.getNodeName()))
		return new TAG_tag_TAG(element, consMap);
	if (Constants.USERLIST_userlist_TAG.equals(element.getNodeName()))
		return new USERLIST_userlist_TAG(element, consMap);
	if (Constants.RULE_rule_TAG.equals(element.getNodeName()))
		return new RULE_rule_TAG(element, consMap);
	if (Constants.BODY_body_TAG.equals(element.getNodeName()))
		return new BODY_body_TAG(element, consMap);
	if (Constants.REWRITE_rewrite_TAG.equals(element.getNodeName()))
		return new REWRITE_rewrite_TAG(element, consMap);
	if (Constants.LEFT_left_TAG.equals(element.getNodeName()))
		return new LEFT_left_TAG(element, consMap);
	if (Constants.TERM_term_TAG.equals(element.getNodeName()))
		return new TERM_term_TAG(element, consMap);
	if (Constants.VAR_var_TAG.equals(element.getNodeName()))
		return new VAR_var_TAG(element, consMap);
	if (Constants.RIGHT_right_TAG.equals(element.getNodeName()))
		return new RIGHT_right_TAG(element, consMap);
	if (Constants.EMPTY_empty_TAG.equals(element.getNodeName()))
		return new EMPTY_empty_TAG(element, consMap);
	if (Constants.CONST_const_TAG.equals(element.getNodeName()))
		return new CONST_const_TAG(element, consMap);
	if (Constants.CONFIG_config_TAG.equals(element.getNodeName()))
		return new CONFIG_config_TAG(element, consMap);
	if (Constants.BAG_Bag_TAG.equals(element.getNodeName()))
		return new BAG_Bag_TAG(element, consMap);
	if (Constants.CELL_cell_TAG.equals(element.getNodeName()))
		return new CELL_cell_TAG(element, consMap);
	if (Constants.KSEQUENCE_KSequence_TAG.equals(element.getNodeName()))
		return new KSEQUENCE_KSequence_TAG(element, consMap);
	if (Constants.LIST_List_TAG.equals(element.getNodeName()))
		return new LIST_List_TAG(element, consMap);
	if (Constants.MAP_Map_TAG.equals(element.getNodeName()))
		return new MAP_Map_TAG(element, consMap);
	if (Constants.SET_Set_TAG.equals(element.getNodeName()))
		return new SET_Set_TAG(element, consMap);
	if (Constants.BUILTINOP_builtinOp_TAG.equals(element.getNodeName()))
		return new BUILTINOP_builtinOp_TAG(element, consMap);
	if (Constants.LISTOFK_ListOfK_TAG.equals(element.getNodeName()))
		return new LISTOFK_ListOfK_TAG(element, consMap);
	if (Constants.MAPITEM_MapItem_TAG.equals(element.getNodeName()))
		return new MAPITEM_MapItem_TAG(element, consMap);
	if (Constants.KEY_key_TAG.equals(element.getNodeName()))
		return new KEY_key_TAG(element, consMap);
	if (Constants.VALUE_value_TAG.equals(element.getNodeName()))
		return new VALUE_value_TAG(element, consMap);
	if (Constants.CONTEXT_context_TAG.equals(element.getNodeName()))
		return new CONTEXT_context_TAG(element, consMap);
	if (Constants.HOLE_hole_TAG.equals(element.getNodeName()))
		return new HOLE_hole_TAG(element, consMap);
	if (Constants.COND_cond_TAG.equals(element.getNodeName()))
		return new COND_cond_TAG(element, consMap);
	if (Constants.LISTITEM_ListItem_TAG.equals(element.getNodeName()))
		return new LISTITEM_ListItem_TAG(element, consMap);
	if (Constants.SETITEM_SetItem_TAG.equals(element.getNodeName()))
		return new SETITEM_SetItem_TAG(element, consMap);
	if (Constants.KAPP_KApp_TAG.equals(element.getNodeName()))
		return new KAPP_KApp_TAG(element, consMap);
	if (Constants.LABEL_label_TAG.equals(element.getNodeName()))
		return new LABEL_label_TAG(element, consMap);
	
		return null;
	}

}
