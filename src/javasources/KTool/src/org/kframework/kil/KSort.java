package org.kframework.kil;

public enum KSort {
    K, Bag, BagItem, KItem, KList, CellLabel, KLabel, ;

    public static KSort getKSort(String sort) {
        try {
            return valueOf(sort);
        } catch (Exception e) {
            return K;
        }
    }

    public KSort mainSort() {
        switch (this) {
        case Bag:
        case BagItem:
            return Bag;
        case KItem:
            return K;
        default:
            return this;
        }
    }

    public boolean isDefaultable() {
        return (this == Bag || this == K);
    }
}
