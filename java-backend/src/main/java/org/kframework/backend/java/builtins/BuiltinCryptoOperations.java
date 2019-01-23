// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;


import org.apache.commons.codec.binary.StringUtils;
import org.bouncycastle.jcajce.provider.digest.Keccak;
import org.bouncycastle.jcajce.provider.digest.SHA256;
import org.bouncycastle.jcajce.provider.digest.SHA3;
import org.bouncycastle.jcajce.provider.digest.RIPEMD160;
import org.bouncycastle.util.encoders.Hex;
import org.kframework.kore.K;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.builtins.crypto.ECDSARecover;
import org.kframework.backend.java.builtins.crypto.BN128;
import org.kframework.backend.java.builtins.crypto.BN128Fp;
import org.kframework.backend.java.builtins.crypto.BN128G1;
import org.kframework.backend.java.builtins.crypto.BN128G2;
import org.kframework.backend.java.builtins.crypto.Fp;
import org.kframework.backend.java.builtins.crypto.PairingCheck;
import org.kframework.kore.KORE;

import java.math.BigInteger;
import java.security.SignatureException;
import java.util.Arrays;

/**
 * Builtins for Cryptographic Operations
 */
public final class BuiltinCryptoOperations {

    /**
     * Finds the keccak256 digest of the input.
     *
     * @param inputString - The String is expected to be formed such that each character in the string
     *                       represents a Latin-1 encoded byte.
     * @return Output String (256 characters) such that each character represents an encoded Hex Value.
     */
    public static StringToken keccak256(StringToken inputString, TermContext context) {
        byte[] bytes = StringUtils.getBytesIso8859_1(inputString.stringValue());
        Keccak.Digest256 keccakEngine = new Keccak.Digest256();
        byte[] digest = keccakEngine.digest(bytes);
        String digestString = Hex.toHexString(digest);
        return StringToken.of(digestString);
    }

    /**
     * Finds the SHA3 digest of the input.
     *
     * @param inputString - The String is expected to be formed such that each character in the string
     *                       represents a Latin-1 encoded byte.
     * @return Output String (256 characters) such that each character represents an encoded Hex Value.
     */
    public static StringToken sha3256(StringToken inputString, TermContext context) {
        byte[] bytes = StringUtils.getBytesIso8859_1(inputString.stringValue());
        SHA3.Digest256 sha3engine = new SHA3.Digest256();
        byte[] digest = sha3engine.digest(bytes);
        String digestString = Hex.toHexString(digest);
        return StringToken.of(digestString);
    }

    /**
     * Finds the SHA256 digest of the input.
     *
     * @param inputString - The String is expected to be formed such that each character in the string
     *                       represents a Latin-1 encoded byte.
     * @return Output String (256 characters) such that each character represents an encoded Hex Value.
     */
    public static StringToken sha256(StringToken inputString, TermContext context) {
        byte[] bytes = StringUtils.getBytesIso8859_1(inputString.stringValue());
        SHA256.Digest sha2engine = new SHA256.Digest();
        byte[] digest = sha2engine.digest(bytes);
        String digestString = Hex.toHexString(digest);
        return StringToken.of(digestString);
    }

    /**
     * Finds the RIPEMD160 digest of the input.
     *
     * @param inputString - The String is expected to be formed such that each character in the string
     *                       represents a Latin-1 encoded byte.
     * @return Output String (256 characters) such that each character represents an encoded Hex Value.
     */
    public static StringToken ripemd160(StringToken inputString, TermContext context) {
        byte[] bytes = StringUtils.getBytesIso8859_1(inputString.stringValue());
        RIPEMD160.Digest ripemd160engine = new RIPEMD160.Digest();
        byte[] digest = ripemd160engine.digest(bytes);
        String digestString = Hex.toHexString(digest);
        return StringToken.of(digestString);
    }

    /**
     * Recovers the ECDSA Public key from a message hash and signature
     * @param messageHash a 32-character string in Latin-1 encoding representing the 32-byte message hash of the signed message
     * @param v The recovery id, in the range 27-34, to use to recover the correct public key
     * @param r The r component of the message signature, as a 32-character Latin-1 string
     * @param s The s component of the message signature, as a 32-character Latin-1 string
     * @return Output String (64 characters) in Latin-1 encoding representing the public key recovered upon success. Returns
     *         the empty string if key recovery fails due to invalid input.
     * */
    public static StringToken ecdsaRecover(StringToken messageHash, IntToken v, StringToken r, StringToken s, TermContext context) {
        byte[] hashBytes = StringUtils.getBytesIso8859_1(messageHash.stringValue());
        byte vByte = v.bigIntegerValue().byteValueExact();
        byte[] rBytes = StringUtils.getBytesIso8859_1(r.stringValue());
        byte[] sBytes = StringUtils.getBytesIso8859_1(s.stringValue());
        try {
            ECDSARecover key = ECDSARecover.signatureToKey(hashBytes, rBytes, sBytes, vByte);
            return StringToken.of(Arrays.copyOfRange(key.getPubKey(), 1, 65));
        } catch (SignatureException | IllegalArgumentException e) {
            return StringToken.of("");
        }
    }

    private static BigInteger getCoord(KItem kitem, int idx) {
        K item = kitem.items().get(idx);
        if (!(item instanceof IntToken)) {
           return null;
        }
        return ((IntToken)item).bigIntegerValue();
    }


    private static KItem mkPoint(Fp x, Fp y, GlobalContext global) {
        KLabelConstant G1_POINT_KLABEL = KLabelConstant.of(KORE.KLabel("(_,_)"), global.getDefinition());
        return KItem.of(G1_POINT_KLABEL, KList.concatenate(IntToken.of(x.v()), IntToken.of(y.v())), global);
    }

    public static KItem bn128add(KItem point1, KItem point2, TermContext context) {
        BigInteger x1 = getCoord(point1, 0);
        BigInteger y1 = getCoord(point1, 1);
        BigInteger x2 = getCoord(point2, 0);
        BigInteger y2 = getCoord(point2, 1);
        if (x1 == null || x2 == null || y1 == null || y2 == null) {
            return null;
        }
        BN128<Fp> p1 = BN128Fp.create(x1, y1);
        BN128<Fp> p2 = BN128Fp.create(x2, y2);
        if (p1 == null || p2 == null) {
            return null;
        }
        BN128<Fp> res = p1.add(p2).toEthNotation();
        return mkPoint(res.x(), res.y(), context.global());
    }

    public static KItem bn128mul(KItem point, IntToken scalar, TermContext context) {
        BigInteger x = getCoord(point, 0);
        BigInteger y = getCoord(point, 1);
        if (x == null || y == null) {
            return null;
        }
        BN128<Fp> p = BN128Fp.create(x, y);
        if (p == null) {
            return null;
        }
        BN128<Fp> res = p.mul(scalar.bigIntegerValue()).toEthNotation();
        return mkPoint(res.x(), res.y(), context.global());
    }

    public static BoolToken bn128valid(KItem point, TermContext context) {
        BigInteger x = getCoord(point, 0);
        BigInteger y = getCoord(point, 1);
        if (x == null || y == null) {
            return null;
        }
        BN128G1 p = BN128G1.create(x, y);
        return BoolToken.of(p != null);
    }

    public static BoolToken bn128g2valid(KItem point, TermContext context) {
        BigInteger x1 = getCoord(point, 0);
        BigInteger x2 = getCoord(point, 1);
        BigInteger y1 = getCoord(point, 2);
        BigInteger y2 = getCoord(point, 3);
        if (x1 == null || x2 == null || y1 == null || y2 == null) {
            return null;
        }
        BN128G2 p = BN128G2.create(x2, x1, y2, y1);
        return BoolToken.of(p != null);
    }

    public static BoolToken bn128ate(BuiltinList g1, BuiltinList g2, TermContext context) {
        if (!g1.isConcreteCollection() || !g2.isConcreteCollection() || g1.size() != g2.size()) {
            return null;
        }
        PairingCheck check = PairingCheck.create();
        for (int i = 0; i < g1.size(); i++) {
            Term term1 = g1.children.get(i);
            Term term2 = g2.children.get(i);
            if (!(term1 instanceof KItem) || !(term2 instanceof KItem)) {
                return null;
            }
            KItem point1 = (KItem) term1;
            KItem point2 = (KItem) term2;
            BigInteger x = getCoord(point1, 0);
            BigInteger y = getCoord(point1, 1);
            if (x == null || y == null) {
                return null;
            }
            BigInteger x1 = getCoord(point2, 0);
            BigInteger x2 = getCoord(point2, 1);
            BigInteger y1 = getCoord(point2, 2);
            BigInteger y2 = getCoord(point2, 3);
            if (x1 == null || x2 == null || y1 == null || y2 == null) {
                return null;
            }
            BN128G1 p1 = BN128G1.create(x, y);
            if (p1 != null) {
                return null;
            }
            BN128G2 p2 = BN128G2.create(x2, x1, y2, y1);
            if (p2 == null) {
                return null;
            }
            check.addPair(p1, p2);
        }
        check.run();
        return BoolToken.of(check.result() != 0);
    }
}
