// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.ktest.Test;

import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.ktest.KTestStep;
import org.kframework.ktest.Proc;
import org.kframework.utils.OS;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.PriorityBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

/**
 * Just a fancy wrapper around {@link java.util.concurrent.ThreadPoolExecutor}
 * to provide a specialized version for KTest's needs.
 *
 * Namely, a basic concurrent task in KTest is a TestCase. This class handles splitting a TestCase
 * into {@link org.kframework.ktest.Proc}s and pass it to
 * {@link java.util.concurrent.ThreadPoolExecutor} in a way that provide us good concurrency.
 * (e.g. it tries to minimize threads waiting idle)
 *
 * TaskQueue makes sure that no thread in {@link java.util.concurrent.ThreadPoolExecutor} will wait
 * idle unless:
 * - krun processes are blocked because their definitions are being compiled.
 * - There are no more tasks to run.
 */
public class TaskQueue {

    private final KTestOptions options;

    // TODO: tpe.execute() assumed to be thread-safe. Make sure this is correct, or add syncronized
    // wrapper around it.
    private final ThreadPoolExecutor tpe;

    /**
     * Status of a kompile task. See {@link #kompilePaths}.
     */
    private enum KompileStatus {
        NOT_STARTED, IN_PROGRESS, FAILED, SUCCEEDED
    }

    /**
     * ktest tries to avoid redundant compilations by checking if a compilation to the same path
     * is happened before. Note that tests that make compilations to same directory
     * (e.g. tests that result in generation of same "-kompiled" directories multiple times)
     * may result in race conditions, so this behavior is correct:
     * Test writers should make sure that no compilation is happening to same directory, unless
     * compiled definition is same and same options are used for compilation.
     *
     * We also need to keep track of running kompile processes to prevent spawning threads that
     * do same compilation. Value part of the map handles all possibilities.
     */
    private final Map<String, KompileStatus> kompilePaths = new ConcurrentHashMap<>();

    /**
     * Similarly, we keep track of PDF tasks. PDF tasks are easier to handle, because we don't
     * need to keep track of in-progress tasks(no other tasks depend on successful PDF tasks so
     * no need to wait until a PDF task is finished, we can just skip the step since we know
     * same PDF task is either in-progress or already done).
     *
     * Another difference is that we don't keep track of target PDF file paths, but rather we
     * keep track of .k file paths. This is because we assume every definition file has one unique
     * PDF file.
     *
     * Boolean part indicates success of the task.
     */
    private final Map<String, Boolean> pdfDefs = new ConcurrentHashMap<>();

    /*
     * We keep track of Proc objects we run to be able to generate statistics/print useful info
     * after we're done.
     *
     * Note that these don't hold all the Proc objects, hold only the ones that we really run.
     */
    private final List<Proc<TestCase>> scriptProcs = Collections.synchronizedList(new ArrayList<>());
    private final List<Proc<TestCase>> kompileProcs = Collections.synchronizedList(new ArrayList<>());
    private final List<Proc<TestCase>> pdfProcs = Collections.synchronizedList(new ArrayList<>());
    private final List<Proc<KRunProgram>> krunProcs = Collections.synchronizedList(new ArrayList<>());

    /**
     * Time when lastly finished task finishes.
     * Set using {@link java.lang.System#currentTimeMillis}.
     */
    private long lastTestFinished;

    public TaskQueue(KTestOptions options) {
        this.options = options;
        int nThreads;
        if (options.getUpdateOut() || options.getGenerateOut()) {
            nThreads = 1;
        } else {
            nThreads = options.getThreads();
        }
        this.tpe = new ThreadPoolExecutor(nThreads, nThreads, 0L, TimeUnit.MILLISECONDS, new PriorityBlockingQueue<>());
    }

    /**
     * Add a test case to the task queue.
     * @param tc TestCase to add to the task queue.
     */
    public void addTask(TestCase tc) {
        if (OS.current().isPosix && tc.getPosixInitScript() != null) {
            Proc<TestCase> proc = tc.getPosixOnlyProc();
            tpe.execute(wrapScriptStep(proc));
        } else {
            continueFromKompileStep(tc);
        }
    }

    /**
     * Block until all threads are done. Adding new tasks after this results in exception.
     */
    public void terminate() {
        try {
            while (!tpe.awaitTermination(1, TimeUnit.SECONDS)) {
                if (tpe.getActiveCount() == 0) {
                    tpe.shutdown();
                    return;
                }
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw KExceptionManager.criticalError("KTest was interrupted", e);
        }
    }

    public List<Proc<TestCase>> getScriptProcs() {
        return scriptProcs;
    }

    public List<Proc<TestCase>> getKompileProcs() {
        return kompileProcs;
    }

    public List<Proc<TestCase>> getPdfProcs() {
        return pdfProcs;
    }

    public List<Proc<KRunProgram>> getKrunProcs() {
        return krunProcs;
    }

    public long getLastTestFinished() {
        return lastTestFinished;
    }

    /**
     * Continue running the test case from kompile step. Also runs PDF step.
     * krun steps are added to the queue by successfully terminated kompile steps. If we're skipping
     * kompile steps(either because of `--skip kompile` or setting in config file) then this
     * method adds krun steps to the queue.
     * @param tc TestCase to continue running.
     */
    private void continueFromKompileStep(TestCase tc) {
        if (!options.getSkips().contains(KTestStep.KOMPILE) && !tc.skip(KTestStep.KOMPILE)) {
            executeKompileStep(tc);
        } else {
            // Normally, krun steps of a test case is added after kompile step of the test case is
            // done. But since we just skipped kompile step, we need to add krun steps here
            addKRunSteps(tc);
        }
    }

    /**
     * Execute a kompile step of the given test case. krun steps will be added if ktest step
     * is successfully terminates.
     * @param tc TestCase to execute kompile step.
     */
    private void executeKompileStep(TestCase tc) {
        Proc<TestCase> proc = tc.getKompileProc();
        tpe.execute(wrapKompileStep(proc));
    }

    /**
     * Create a {@link java.lang.Runnable} from a script step that, after successfully running,
     * adds kompile step that depends on the script. Also adds script
     * {@link org.kframework.ktest.Proc} object to {@link #scriptProcs}.
     * @param scriptStep Script step to wrap.
     * @return New {@link java.lang.Runnable} that does things described above.
     */
    private KTestQueueItem wrapScriptStep(Proc<TestCase> scriptStep) {
        return new KTestQueueItem() {
            @Override
            public void run() {
                scriptProcs.add(scriptStep);
                scriptStep.run();
                if (scriptStep.isSuccess()) {
                    continueFromKompileStep(scriptStep.getObj());
                }
            }

            @Override
            protected int priority() {
                return 1;
            }
        };
    }

    /**
     * Create a {@link java.lang.Runnable} from a kompile step that, before running:
     * - Adds the step to {@link #kompilePaths}.
     * After running:
     * - Adds krun tasks that depend on this kompile step to the queue. (only if it's
     *   successfully done)
     * - Updates {@link #kompilePaths}.
     * - Adds Proc to {@link #kompileProcs}.
     * - Updates {@link #lastTestFinished}.
     * @param kompileStep Kompile step to wrap.
     * @return New {@link java.lang.Runnable} that does things described above.
     */
    private KTestQueueItem wrapKompileStep(Proc<TestCase> kompileStep) {
        return new KTestQueueItem() {
            @Override
            public void run() {
                String kompilePath = kompileStep.getObj().getKompileDirFullPath();
                KompileStatus status = tryAddKompileInProgress(kompilePath);
                if (status == KompileStatus.NOT_STARTED) {
                    // We're running the kompile process
                    kompileProcs.add(kompileStep);
                    kompileStep.run();
                    lastTestFinished = System.currentTimeMillis();
                    boolean success = kompileStep.isSuccess();
                    synchronized (TaskQueue.this) {
                        kompilePaths.put(kompilePath,
                                success ? KompileStatus.SUCCEEDED : KompileStatus.FAILED);
                    }
                    if (success) {
                        addKRunSteps(kompileStep.getObj());
                    }
                } else if (status == KompileStatus.IN_PROGRESS) {
                    // Just wait until it's finished
                    tpe.execute(this);
                } else if (status == KompileStatus.SUCCEEDED) {
                    // Just add KRun steps
                    addKRunSteps(kompileStep.getObj());
                } else if (status == KompileStatus.FAILED) {
                    // Nothing to do
                } else {
                    throw new RuntimeException("Unhandled case in TaskQueue.wrapKompileStep");
                }
            }

            @Override
            protected int priority() {
                return 1;
            }
        };
    }

    private static abstract class KTestQueueItem implements Runnable, Comparable<KTestQueueItem> {

        protected abstract int priority();

        @Override
        public int compareTo(KTestQueueItem o) {
            return Integer.compare(priority(), o.priority());
        }

    }

    /**
     * Check status of kompile task that compiles to given path.
     * Path is added to {@link #kompilePaths} as {@code IN_PROGRESS} when {@code NOT_STARTED}
     * is returned.
     * @param path Path to search in {@link #kompilePaths}.
     * @return Status of kompile task that compiles to given path. Never returns {@code NOT_STARTED}.
     */
    private synchronized KompileStatus tryAddKompileInProgress(String path) {
        KompileStatus status = kompilePaths.get(path);
        assert (status != KompileStatus.NOT_STARTED)
                : "TaskQueue.kompilePaths: Kompile task shouldn't be in NOT_STARTED state";
        if (status == null) {
            kompilePaths.put(path, KompileStatus.IN_PROGRESS);
            return KompileStatus.NOT_STARTED;
        }
        return status;
    }

    /**
     * Create a {@link java.lang.Runnable} from a PDF step that updates {@link #pdfDefs},
     * {@link #pdfProcs} and {@link #lastTestFinished} after it's done.
     * @param pdfStep PDF step to wrap.
     * @return New {@link java.lang.Runnable} that does things described above.
     */
    private KTestQueueItem wrapPDFStep(Proc<TestCase> pdfStep) {
        return new KTestQueueItem() {
            @Override
            public void run() {
                pdfDefs.put(pdfStep.getObj().getDefinition(), pdfStep.isSuccess());
                pdfProcs.add(pdfStep);
                pdfStep.run();
                lastTestFinished = System.currentTimeMillis();
            }

            @Override
            protected int priority() {
                return 1;
            }
        };
    }

    /**
     * Add KRun steps of the given test case to the {@link #tpe}, unless krun steps are skipped.
     * (using `--skip krun` or setting in the config file)
     */
    private void addKRunSteps(TestCase tc) {
        if (!options.getSkips().contains(KTestStep.KRUN) && !tc.skip(KTestStep.KRUN)) {
            for (Proc<KRunProgram> proc : tc.getKRunProcs()) {
                tpe.execute(wrapKRunStep(proc));
            }
        }
        if (!options.getSkips().contains(KTestStep.PDF) && !tc.skip(KTestStep.PDF)
                && !pdfDefs.containsKey(tc.getDefinition())) {
            Proc<TestCase> proc = tc.getPDFProc();
            tpe.execute(wrapPDFStep(proc));
            pdfDefs.put(tc.getDefinition(), false);
        }
    }

    /**
     * Create a {@link java.lang.Runnable} from a krun step that updates {@link #krunProcs} and
     * {@link #lastTestFinished}.
     * @param krunStep KRun step to wrap.
     * @return New {@link java.lang.Runnable} that does things described above.
     */
    private KTestQueueItem wrapKRunStep(Proc<KRunProgram> krunStep) {
        return new KTestQueueItem() {
            @Override
            public void run() {
                // Don't check for `-kompiled` directory when in --dry mode. This is because
                // in --dry we never create directories, so this check will always return false.
                if (options.dry ||
                        krunStep.getObj().testCase.isDefinitionKompiled()) {
                    krunProcs.add(krunStep);
                    krunStep.run();
                    lastTestFinished = System.currentTimeMillis();
                } else {
                    executeKompileStep(krunStep.getObj().testCase);
                }
            }

            @Override
            protected int priority() {
                return 0;
            }
        };
    }
}

