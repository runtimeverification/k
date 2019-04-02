// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;

/**
 * @author Denis Bogdanas
 * Created on 30-Jan-19.
 * <p>
 * Arguments {@code intermediateStats} are needed to remove explicit GC times that happened in the processed interval.
 * It is the duty of calling code to provide them correctly.
 */
public class TimeMemoryEntry {

    private static final double BILLION = 1000000000.;
    /**
     * Main TimeMemoryEntry for the moment.
     */
    SubEntry main;

    /**
     * TimeMemoryEntry after System.gc() invocation.
     */
    SubEntry postGC;

    public TimeMemoryEntry(boolean callGC) {
        main = new SubEntry();
        if (callGC) {
            System.gc();
            postGC = new SubEntry();
        }
    }

    public TimeMemoryEntry(long timeNano) {
        main = new SubEntry(timeNano);
    }

    private SubEntry last() {
        return postGC != null ? postGC : main;
    }

    public double timeDiff(TimeMemoryEntry startStats, TimeMemoryEntry... intermediateStats) {
        double result = main.timeDiff(startStats.last());
        for (TimeMemoryEntry intermediateStat : intermediateStats) {
            result -= intermediateStat.last().timeDiff(intermediateStat.main);
        }
        return result;
    }

    public long gcTimeMillisDiff(TimeMemoryEntry init, TimeMemoryEntry... intermediateStats) {
        long result = main.gcTimeMillisDiff(init.last());
        for (TimeMemoryEntry intermediateStat : intermediateStats) {
            result -= intermediateStat.last().gcTimeMillisDiff(intermediateStat.main);
        }
        return result;
    }

    public long usedPostGCMemory() {
        return postGC.usedMemory();
    }

    /**
     * @return string representing time, memory used, GC percent time. Time and GC percent are for interval
     * [this] - [init].
     * {@code intermediateStats} are needed to eliminate intermediate explicit GC data.
     */
    public String logString(TimeMemoryEntry init, TimeMemoryEntry... intermediateStats) {
        double time = timeDiff(init, intermediateStats);
        long memory = main.usedMemory();
        double timeMillis = time * 1000;
        double gcRate = timeMillis > 0 ? ((double) gcTimeMillisDiff(init, intermediateStats)) / timeMillis * 100 : 0;

        return String.format("%8.3f s,\t%5d MB, gc: %6.3f %%", time, memory, gcRate);
    }

    /**
     * @return string representing post-gc memory stats - post-gc memory and explicit gc time.
     * If there is no post-GC entry, return empty string.
     */
    public String postGCLogString(String prefix, TimeMemoryEntry... intermediateStats) {
        if (postGC == null) {
            return "";
        }
        long memory = postGC.usedMemory();
        double gcTime = postGC.timeDiff(main);
        for (TimeMemoryEntry intermediateStat : intermediateStats) {
            gcTime += intermediateStat.last().timeDiff(intermediateStat.main);
        }

        return String.format("%s%5d MB,   exp gc time: %6.3f s", prefix, memory, gcTime);
    }

    /**
     * Return string containing time since start, memory used, GC percent time since previous step.
     */
    public String stepLogString(TimeMemoryEntry init, TimeMemoryEntry prevStep) {
        double time = timeDiff(init);
        long memory = main.usedMemory();
        double timeMillis = timeDiff(prevStep) * 1000;
        double gcRate = timeMillis > 0 ? ((double) (gcTimeMillisDiff(prevStep))) / timeMillis * 100 : 0;

        return String.format("%8.3f s, \t\t%5d MB, gc: %6.3f %%", time, memory, gcRate);
    }

    private static class SubEntry {
        //All stats are for the whole VM since the beginning of execution, at the moment of constructor invocation.
        public final long timeNano;
        public final long totalMemory;
        public final long freeMemory;
        public final long gcCount;
        public final long gcTimeMillis;
        public final long gcCountOldGen;
        public final long gcTimeMillisOldGen;

        private SubEntry() {
            timeNano = System.nanoTime();
            totalMemory = Runtime.getRuntime().totalMemory();
            freeMemory = Runtime.getRuntime().freeMemory();

            long gcCount = 0;
            long gcTime = 0;
            long gcCountOldGen = 0;
            long gcTimeMillisOldGen = 0;
            for (GarbageCollectorMXBean bean : ManagementFactory.getGarbageCollectorMXBeans()) {
                gcCount += bean.getCollectionCount();
                gcTime += bean.getCollectionTime();
                if (isOldGenGC(bean)) {
                    gcCountOldGen += bean.getCollectionCount();
                    gcTimeMillisOldGen += bean.getCollectionTime();
                }
            }
            this.gcCount = gcCount;
            this.gcTimeMillis = gcTime;
            this.gcCountOldGen = gcCountOldGen;
            this.gcTimeMillisOldGen = gcTimeMillisOldGen;
        }

        /**
         * @return true if the garbage collector represented by this bean manages the old generation.
         * <p>
         * Old generation memory pools have name that ends with either "Old Gen" or "Tenured Gen" in all known Java GC
         * algorithms: https://gist.github.com/szegedi/1474365/ebee66b04aa3468b5e3864945dc48fa3e204548a
         */
        private boolean isOldGenGC(GarbageCollectorMXBean bean) {
            for (String poolName : bean.getMemoryPoolNames()) {
                if (poolName.endsWith("Old Gen") || (poolName.endsWith("Tenured Gen"))) {
                    return true;
                }
            }
            return false;
        }

        /**
         * For init time only.
         */
        private SubEntry(long timeNano) {
            this.timeNano = timeNano;
            totalMemory = 0;
            freeMemory = 0;
            gcCount = 0;
            gcTimeMillis = 0;
            gcCountOldGen = 0;
            gcTimeMillisOldGen = 0;
        }

        /**
         * @return Time difference in seconds.
         */
        private double timeDiff(SubEntry init) {
            return (timeNano - init.timeNano) / BILLION;
        }

        private long gcTimeMillisDiff(SubEntry init) {
            return gcTimeMillisOldGen - init.gcTimeMillisOldGen;
        }

        private long usedMemory() {
            return (totalMemory - freeMemory) / (1024 * 1024);
        }
    }
}
