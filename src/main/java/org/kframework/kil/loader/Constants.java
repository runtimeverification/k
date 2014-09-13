// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import java.util.HashMap;
import java.util.Map;

/**
 * @author andrei.arusoaie
 *
 */
public class Constants {

    // Tags constants
    public static final String RULE = "rule";
    public static final String SENTENCE = "sentence";
    public static final String BODY = "body";
    public static final String REWRITE = "rewrite";
    public static final String LEFT = "left";
    public static final String TERM = "term";
    public static final String SYN = "Syn";
    public static final String BRACKET = "bracket";
    public static final String CAST = "cast";
    public static final String VAR = "var";
    public static final String VARIABLE = "variable";
    public static final String RIGHT = "right";
    public static final String ATTRIBUTES = "attributes";
    public static final String TAG = "tag";
    public static final String CONST = "const";
    public static final String KAPP = "KApp";
    public static final String LABEL = "label";
    public static final String EMPTY = "empty";
    public static final String COND = "cond";
    public static final String BUILTINOP = "builtinOp";
    public static final String CONFIG = "config";
    public static final String CELL = "cell";
    public static final String K = "K";
    public static final String KSEQUENCE = "KSequence";
    public static final String KEY = "key";
    public static final String VALUE = "value";
    public static final String CONTEXT = "context";
    public static final String HOLE = "hole";
    public static final String FREEZERHOLE = "freezerHole";
    public static final String DEFINITION = "def";
    public static final String AMB = "amb";
    public static final String MAINFILE = "mainFile";
    public static final String MAINMODULE = "mainModule";
    public static final String MAINSYNTAXMODULE = "mainSyntaxModule";
    public static final String NAME = "name";
    public static final String PREDICATE = "predicate";
    public static final String NON_ASSOC = "non-assoc";
    // Attributes constants
    public static final String VALUE_value_ATTR = "value";
    public static final String LOC_loc_ATTR = "loc";
    public static final String TYPE_type_ATTR = "type";
    public static final String TYPE_userTyped_ATTR = "userTyped";
    public static final String FILENAME_filename_ATTR = "filename";
    public static final String NAME_name_ATTR = "name";
    public static final String SORT_sort_ATTR = "sort";
    public static final String CONS_cons_ATTR = "cons";
    public static final String KEY_key_ATTR = "key";
    public static final String ASSOC_assoc_ATTR = "assoc";
    public static final String SEPARATOR_separator_ATTR = "separator";
    public static final String COLOR_color_ATTR = "color";
    public static final String LABEL_label_ATTR = "label";
    public static final String ENDLABEL_label_ATTR = "endLabel";
    public static final String MULTIPLICITY_multiplicity_ATTR = "multiplicity";
    public static final String ELLIPSES_ellipses_ATTR = "ellipses";
    public static final String SHARED = "SHARED";
    public static final String PREDEFINED = "predefined";
    public static final String BREAK = "br";
    public static final String BAG = "Bag";
    public static final String BAG_ITEM = "BagItem";
    public static final String KLIST = "KList";
    public static final String MACRO = "macro";
    public static final String STRUCTURAL = "structural";
    public static final String FUNCTION = "function";
    public static final String ANYWHERE = "anywhere";
    public static final String REGEX = "regex";
    public static final String SOURCE_ATTR = "source";

    // Streams
    public static final String STDIN = "stdin";
    public static final String STDOUT = "stdout";
    public static final String STDERR = "stderr";

    // Generated stuff
    public static final String GENERATED_FILENAME = "File System";
    public static final String GENERATED_LOCATION = "generated";
    public static final Map<String,String> defaultAttributeValues = new HashMap<String, String>();
    public static final String ERROR = "error";

    static {
        defaultAttributeValues.put("filename", Constants.GENERATED_FILENAME);
        defaultAttributeValues.put("location", Constants.GENERATED_LOCATION);
    }

    static final String AUTO_INCLUDED_MODULE = "AUTO-INCLUDED-MODULE";
    public static String AUTO_INCLUDED_SYNTAX_MODULE = "AUTO-INCLUDED-MODULE-SYNTAX";
}
