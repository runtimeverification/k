package org.kframework.parser.generator.basic;

import java.util.*;

public class Cell implements java.io.Serializable {
	private static final long serialVersionUID = 1L;
	private String label;
	private String sort;
	private Map<String, String> attributes;

	public Cell() {
		attributes = new HashMap<String, String>();
	}

	public Cell(String label, String sort) {
		this.label = label;
		this.sort = sort;
	}

	public String getLabel() {
		return label;
	}

	public void setLabel(String label) {
		this.label = label;
	}

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	public Map<String, String> getAttributes() {
		return attributes;
	}

	public void setAttributes(Map<String, String> attributes) {
		this.attributes = attributes;
	}
}
