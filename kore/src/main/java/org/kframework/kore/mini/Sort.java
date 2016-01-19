package org.kframework.kore.mini;

public class Sort implements org.kframework.kore.Sort {
    private final String name;

    public Sort(String name) {
        this.name = name;
    }

    @Override
    public String name() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Sort sort = (Sort) o;

        return name.equals(sort.name);

    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }
}
