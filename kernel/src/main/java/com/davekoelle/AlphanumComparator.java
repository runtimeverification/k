/*
 * The Alphanum Algorithm is an improved sorting algorithm for strings
 * containing numbers.  Instead of sorting numbers in ASCII order like
 * a standard sort, this algorithm sorts numbers in numeric order.
 *
 * The Alphanum Algorithm is discussed at http://www.DaveKoelle.com
 *
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

package com.davekoelle;

import java.util.Comparator;

/**
 * This is an updated version with enhancements made by Daniel Migowski,
 * Andre Bogus, and David Koelle
 *
 * To convert to use Templates (Java 1.5+):
 *   - Change "implements Comparator" to "implements Comparator<String>"
 *   - Change "compare(Object o1, Object o2)" to "compare(String s1, String s2)"
 *   - Remove the type checking and casting in compare().
 *
 * To use this class:
 *   Use the static "sort" method from the java.util.Collections class:
 *   Collections.sort(your list, new AlphanumComparator());
 */
public class AlphanumComparator implements Comparator<String>
{
    private final boolean isDigit(char ch)
    {
        return ch >= 48 && ch <= 57;
    }

    /** Length of string is passed in for improved efficiency (only need to calculate it once) **/
    private final String getChunk(String s, int slength, int marker)
    {
        StringBuilder chunk = new StringBuilder();
        char c = s.charAt(marker);
        chunk.append(c);
        marker++;
        if (isDigit(c))
        {
            while (marker < slength)
            {
                c = s.charAt(marker);
                if (!isDigit(c))
                    break;
                chunk.append(c);
                marker++;
            }
        } else
        {
            while (marker < slength)
            {
                c = s.charAt(marker);
                if (isDigit(c))
                    break;
                chunk.append(c);
                marker++;
            }
        }
        return chunk.toString();
    }

    public int compare(String o1, String o2)
    {
        if (!(o1 instanceof String) || !(o2 instanceof String))
        {
            return 0;
        }
        String s1 = (String)o1;
        String s2 = (String)o2;

        int thisMarker = 0;
        int thatMarker = 0;
        int s1Length = s1.length();
        int s2Length = s2.length();

        while (thisMarker < s1Length && thatMarker < s2Length)
        {
            String thisChunk = getChunk(s1, s1Length, thisMarker);
            thisMarker += thisChunk.length();

            String thatChunk = getChunk(s2, s2Length, thatMarker);
            thatMarker += thatChunk.length();

            // If both chunks contain numeric characters, sort them numerically
            int result = 0;
            if (isDigit(thisChunk.charAt(0)) && isDigit(thatChunk.charAt(0)))
            {
                // Simple chunk comparison by length.
                int thisChunkLength = thisChunk.length();
                result = thisChunkLength - thatChunk.length();
                // If equal, the first different number counts
                if (result == 0)
                {
                    for (int i = 0; i < thisChunkLength; i++)
                    {
                        result = thisChunk.charAt(i) - thatChunk.charAt(i);
                        if (result != 0)
                        {
                            return result;
                        }
                    }
                }
            } else
            {
                result = thisChunk.compareTo(thatChunk);
            }

            if (result != 0)
                return result;
        }

        return s1Length - s2Length;
    }

    private final int getChunkLength(String s, int marker, int end)
    {
        int start = marker;
        char c = s.charAt(marker);
        marker++;
        if (isDigit(c))
        {
            while (marker < end)
            {
                c = s.charAt(marker);
                if (!isDigit(c))
                    break;
                marker++;
            }
        } else
        {
            while (marker < end)
            {
                c = s.charAt(marker);
                if (isDigit(c))
                    break;
                marker++;
            }
        }
        return marker - start;
    }

    public int compare(String string, int thisOffsetStart, int thisOffsetEnd,
            int thatOffsetStart, int thatOffsetEnd) {
        int len = string.length();
        if (thisOffsetEnd >= len || thatOffsetEnd >= len) {
            throw new IllegalArgumentException("end offset not within bounds of string");
        }
        int thisMarker = thisOffsetStart;
        int thatMarker = thatOffsetStart;
        int s1Length = thisOffsetEnd - thisOffsetStart;
        int s2Length = thatOffsetEnd - thatOffsetStart;

        while (thisMarker < thisOffsetEnd && thatMarker < thatOffsetEnd)
        {
            int thisChunkLength = getChunkLength(string, thisMarker, thisOffsetEnd);
            int thatChunkLength = getChunkLength(string, thatMarker, thatOffsetEnd);

            // If both chunks contain numeric characters, sort them numerically
            int result = 0;
            if (isDigit(string.charAt(thisMarker)) && isDigit(string.charAt(thatMarker)))
            {
                // Simple chunk comparison by length.
                result = thisChunkLength - thatChunkLength;
                // If equal, the first different number counts
                if (result == 0)
                {
                    for (int i = 0; i < thisChunkLength; i++)
                    {
                        result = string.charAt(thisMarker + i) - string.charAt(thatMarker + i);
                        if (result != 0)
                        {
                            return result;
                        }
                    }
                }
            } else
            {
                int lim = Math.min(thisChunkLength, thatChunkLength);
                int k = 0;
                boolean different = false;
                while (k < lim) {
                    char c1 = string.charAt(thisMarker + k);
                    char c2 = string.charAt(thatMarker + k);
                    if (c1 != c2) {
                        result = c1 - c2;
                        different = true;
                        break;
                    }
                    k++;
                }
                if (!different) {
                    result = thisChunkLength - thatChunkLength;
                }
            }

            thisMarker += thisChunkLength;
            thatMarker += thatChunkLength;

            if (result != 0)
                return result;
        }

        return s1Length - s2Length;
    }
}
