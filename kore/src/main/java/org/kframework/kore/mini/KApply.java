// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.kore.mini;

import org.kframework.attributes.Att;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;

import java.util.AbstractList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

/**
 * Created by dwightguth on 1/11/16.
 */
public abstract class KApply extends AbstractList implements org.kframework.kore.KApply, KList {

    private final KLabel klabel;

    public KApply(KLabel klabel) {
        this.klabel = klabel;
    }

    public static org.kframework.kore.KApply of(KLabel klabel, K... items) {
        switch(items.length) {
        case 0:
            return new KApply0(klabel);
        case 1:
            return new KApply1(klabel, items[0]);
        case 2:
            return new KApply2(klabel, items[0], items[1]);
        case 3:
            return new KApply3(klabel, items[0], items[1], items[2]);
        case 4:
            return new KApply4(klabel, items[0], items[1], items[2], items[3]);
        case 5:
            return new KApply5(klabel, items[0], items[1], items[2], items[3], items[4]);
        case 6:
            return new KApply6(klabel, items[0], items[1], items[2], items[3], items[4], items[5]);
        case 7:
            return new KApply7(klabel, items[0], items[1], items[2], items[3], items[4], items[5], items[6]);
        case 8:
            return new KApply8(klabel, items[0], items[1], items[2], items[3], items[4], items[5], items[6], items[7]);
        case 9:
            return new KApply9(klabel, items[0], items[1], items[2], items[3], items[4], items[5], items[6], items[7],
                    items[8]);
        case 10:
            return new KApply10(klabel, items[0], items[1], items[2], items[3], items[4], items[5], items[6], items[7],
                    items[8], items[9]);
        default:
            return new KApplyGreaterThan10(klabel, items);
        }
    }

    @Override
    public int cachedHashCode() {
        return hashCode();
    }

    @Override
    public KLabel klabel() {
        return klabel;
    }

    @Override
    public KApply klist() {
        return this;
    }

    @Override
    public List<K> items() {
        return this;
    }

    @Override
    public Iterable<? extends K> asIterable() {
        return this;
    }

    @Override
    public Att att() {
        return Att.empty();
    }

    @Override
    public int computeHashCode() {
        return hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        KApply kApply = (KApply) o;

        return klabel.equals(kApply.klabel);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + klabel.hashCode();
        return result;
    }

    @Override
    public abstract Stream<K> stream();
}

class KApply0 extends KApply {

    public KApply0(KLabel klabel) {
        super(klabel);
    }

    @Override
    public K get(int index) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public int size() {
        return 0;
    }

    @Override
    public Stream<K> stream() {
        return Stream.empty();
    }
}

class KApply1 extends KApply {

    private K _0;

    public KApply1(KLabel klabel, K _0) {
        super(klabel);
        this._0 = _0;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 1;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply1 kApply1 = (KApply1) o;

        return _0.equals(kApply1._0);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        return result;
    }
}

class KApply2 extends KApply {

    private K _0, _1;

    public KApply2(KLabel klabel, K _0, K _1) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 2;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply2 kApply2 = (KApply2) o;

        if (!_0.equals(kApply2._0)) return false;
        return _1.equals(kApply2._1);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        return result;
    }
}

class KApply3 extends KApply {

    private K _0, _1, _2;

    public KApply3(KLabel klabel, K _0, K _1, K _2) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 3;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply3 kApply3 = (KApply3) o;

        if (!_0.equals(kApply3._0)) return false;
        if (!_1.equals(kApply3._1)) return false;
        return _2.equals(kApply3._2);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        return result;
    }
}

class KApply4 extends KApply {

    private K _0, _1, _2, _3;

    public KApply4(KLabel klabel, K _0, K _1, K _2, K _3) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
        this._3 = _3;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        case 3:
            return _3;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 4;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2, _3);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply4 kApply4 = (KApply4) o;

        if (!_0.equals(kApply4._0)) return false;
        if (!_1.equals(kApply4._1)) return false;
        if (!_2.equals(kApply4._2)) return false;
        return _3.equals(kApply4._3);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        result = 31 * result + _3.hashCode();
        return result;
    }
}

class KApply5 extends KApply {

    private K _0, _1, _2, _3, _4;

    public KApply5(KLabel klabel, K _0, K _1, K _2, K _3, K _4) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
        this._3 = _3;
        this._4 = _4;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        case 3:
            return _3;
        case 4:
            return _4;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 5;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2, _3, _4);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply5 kApply5 = (KApply5) o;

        if (!_0.equals(kApply5._0)) return false;
        if (!_1.equals(kApply5._1)) return false;
        if (!_2.equals(kApply5._2)) return false;
        if (!_3.equals(kApply5._3)) return false;
        return _4.equals(kApply5._4);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        result = 31 * result + _3.hashCode();
        result = 31 * result + _4.hashCode();
        return result;
    }
}

class KApply6 extends KApply {

    private K _0, _1, _2, _3, _4, _5;

    public KApply6(KLabel klabel, K _0, K _1, K _2, K _3, K _4, K _5) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
        this._3 = _3;
        this._4 = _4;
        this._5 = _5;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        case 3:
            return _3;
        case 4:
            return _4;
        case 5:
            return _5;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 6;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2, _3, _4, _5);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply6 kApply6 = (KApply6) o;

        if (!_0.equals(kApply6._0)) return false;
        if (!_1.equals(kApply6._1)) return false;
        if (!_2.equals(kApply6._2)) return false;
        if (!_3.equals(kApply6._3)) return false;
        if (!_4.equals(kApply6._4)) return false;
        return _5.equals(kApply6._5);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        result = 31 * result + _3.hashCode();
        result = 31 * result + _4.hashCode();
        result = 31 * result + _5.hashCode();
        return result;
    }
}

class KApply7 extends KApply {

    private K _0, _1, _2, _3, _4, _5, _6;

    public KApply7(KLabel klabel, K _0, K _1, K _2, K _3, K _4, K _5, K _6) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
        this._3 = _3;
        this._4 = _4;
        this._5 = _5;
        this._6 = _6;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        case 3:
            return _3;
        case 4:
            return _4;
        case 5:
            return _5;
        case 6:
            return _6;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 7;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2, _3, _4, _5, _6);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply7 kApply7 = (KApply7) o;

        if (!_0.equals(kApply7._0)) return false;
        if (!_1.equals(kApply7._1)) return false;
        if (!_2.equals(kApply7._2)) return false;
        if (!_3.equals(kApply7._3)) return false;
        if (!_4.equals(kApply7._4)) return false;
        if (!_5.equals(kApply7._5)) return false;
        return _6.equals(kApply7._6);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        result = 31 * result + _3.hashCode();
        result = 31 * result + _4.hashCode();
        result = 31 * result + _5.hashCode();
        result = 31 * result + _6.hashCode();
        return result;
    }
}

class KApply8 extends KApply {

    private K _0, _1, _2, _3, _4, _5, _6, _7;

    public KApply8(KLabel klabel, K _0, K _1, K _2, K _3, K _4, K _5, K _6, K _7) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
        this._3 = _3;
        this._4 = _4;
        this._5 = _5;
        this._6 = _6;
        this._7 = _7;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        case 3:
            return _3;
        case 4:
            return _4;
        case 5:
            return _5;
        case 6:
            return _6;
        case 7:
            return _7;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 8;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2, _3, _4, _5, _6, _7);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply8 kApply8 = (KApply8) o;

        if (!_0.equals(kApply8._0)) return false;
        if (!_1.equals(kApply8._1)) return false;
        if (!_2.equals(kApply8._2)) return false;
        if (!_3.equals(kApply8._3)) return false;
        if (!_4.equals(kApply8._4)) return false;
        if (!_5.equals(kApply8._5)) return false;
        if (!_6.equals(kApply8._6)) return false;
        return _7.equals(kApply8._7);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        result = 31 * result + _3.hashCode();
        result = 31 * result + _4.hashCode();
        result = 31 * result + _5.hashCode();
        result = 31 * result + _6.hashCode();
        result = 31 * result + _7.hashCode();
        return result;
    }
}

class KApply9 extends KApply {

    private K _0, _1, _2, _3, _4, _5, _6, _7, _8;

    public KApply9(KLabel klabel, K _0, K _1, K _2, K _3, K _4, K _5, K _6, K _7, K _8) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
        this._3 = _3;
        this._4 = _4;
        this._5 = _5;
        this._6 = _6;
        this._7 = _7;
        this._8 = _8;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        case 3:
            return _3;
        case 4:
            return _4;
        case 5:
            return _5;
        case 6:
            return _6;
        case 7:
            return _7;
        case 8:
            return _8;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 9;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply9 kApply9 = (KApply9) o;

        if (!_0.equals(kApply9._0)) return false;
        if (!_1.equals(kApply9._1)) return false;
        if (!_2.equals(kApply9._2)) return false;
        if (!_3.equals(kApply9._3)) return false;
        if (!_4.equals(kApply9._4)) return false;
        if (!_5.equals(kApply9._5)) return false;
        if (!_6.equals(kApply9._6)) return false;
        if (!_7.equals(kApply9._7)) return false;
        return _8.equals(kApply9._8);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        result = 31 * result + _3.hashCode();
        result = 31 * result + _4.hashCode();
        result = 31 * result + _5.hashCode();
        result = 31 * result + _6.hashCode();
        result = 31 * result + _7.hashCode();
        result = 31 * result + _8.hashCode();
        return result;
    }
}

class KApply10 extends KApply {

    private K _0, _1, _2, _3, _4, _5, _6, _7, _8, _9;

    public KApply10(KLabel klabel, K _0, K _1, K _2, K _3, K _4, K _5, K _6, K _7, K _8, K _9) {
        super(klabel);
        this._0 = _0;
        this._1 = _1;
        this._2 = _2;
        this._3 = _3;
        this._4 = _4;
        this._5 = _5;
        this._6 = _6;
        this._7 = _7;
        this._8 = _8;
        this._9 = _9;
    }

    @Override
    public K get(int index) {
        switch (index) {
        case 0:
            return _0;
        case 1:
            return _1;
        case 2:
            return _2;
        case 3:
            return _3;
        case 4:
            return _4;
        case 5:
            return _5;
        case 6:
            return _6;
        case 7:
            return _7;
        case 8:
            return _8;
        case 9:
            return _9;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int size() {
        return 10;
    }

    @Override
    public Stream<K> stream() {
        return Stream.of(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApply10 kApply10 = (KApply10) o;

        if (!_0.equals(kApply10._0)) return false;
        if (!_1.equals(kApply10._1)) return false;
        if (!_2.equals(kApply10._2)) return false;
        if (!_3.equals(kApply10._3)) return false;
        if (!_4.equals(kApply10._4)) return false;
        if (!_5.equals(kApply10._5)) return false;
        if (!_6.equals(kApply10._6)) return false;
        if (!_7.equals(kApply10._7)) return false;
        if (!_8.equals(kApply10._8)) return false;
        return _9.equals(kApply10._9);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + _0.hashCode();
        result = 31 * result + _1.hashCode();
        result = 31 * result + _2.hashCode();
        result = 31 * result + _3.hashCode();
        result = 31 * result + _4.hashCode();
        result = 31 * result + _5.hashCode();
        result = 31 * result + _6.hashCode();
        result = 31 * result + _7.hashCode();
        result = 31 * result + _8.hashCode();
        result = 31 * result + _9.hashCode();
        return result;
    }
}

class KApplyGreaterThan10 extends KApply {

    private K[] items;

    public KApplyGreaterThan10(KLabel klabel, K... items) {
        super(klabel);
        this.items = items;
    }

    @Override
    public K get(int index) {
        return items[index];
    }

    @Override
    public int size() {
        return items.length;
    }

    @Override
    public Stream<K> stream() {
        return Arrays.stream(items);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        KApplyGreaterThan10 that = (KApplyGreaterThan10) o;

        // Probably incorrect - comparing Object[] arrays with Arrays.equals
        return Arrays.equals(items, that.items);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + Arrays.hashCode(items);
        return result;
    }
}
