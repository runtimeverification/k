package org.kframework.ktest.Test;

import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.ktest.KTestStep;
import org.kframework.ktest.Proc;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

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
     * We keep track of created Proc objects to be able to generate statistics/print useful info
     * after we're done.
     */
    private final List<Proc<TestCase>> kompileProcs = new ArrayList<>();
    private final List<Proc<TestCase>> pdfProcs = new ArrayList<>();
    private final List<Proc<KRunProgram>> krunProcs = new ArrayList<>();

    public TaskQueue(KTestOptions options) {
        this.options = options;
        int nThreads;
        if (options.getUpdateOut() || options.getGenerateOut()) {
            nThreads = 1;
        } else {
            nThreads = options.getThreads();
        }
        this.tpe = (ThreadPoolExecutor) Executors.newFixedThreadPool(nThreads);
    }

    /**
     * Add a test case to the task queue.
     * @param tc TestCase to add to the task queue.
     */
    public void addTask(TestCase tc) {
        if (!options.getSkips().contains(KTestStep.KOMPILE) && !tc.skip(KTestStep.KOMPILE)) {
            Proc<TestCase> proc = new Proc<>(tc, tc.getKompileCmd(), tc.getWorkingDir(), options);
            kompileProcs.add(proc);
            tpe.execute(wrapKompileStep(proc));
        } else {
            // Normally, krun steps of a test case is added after kompile step of the test case is
            // done. But since we're skipping kompile steps, we need to add krun steps here,
            // unless krun steps are skipped too.
            if (!options.getSkips().contains(KTestStep.KRUN) && !tc.skip(KTestStep.KRUN)) {
                addKRunSteps(tc);
            }
        }
        if (!options.getSkips().contains(KTestStep.KRUN) && !tc.skip(KTestStep.PDF)
                && !pdfDefs.containsKey(tc.getDefinition())) {
            Proc<TestCase> proc = new Proc<>(tc, tc.getPdfCmd(), tc.getWorkingDir(), options);
            pdfProcs.add(proc);
            tpe.execute(wrapPDFStep(proc));
            pdfDefs.put(tc.getDefinition(), false);
        }
    }

    /**
     * Create a {@link java.lang.Runnable} from a kompile step that, before running:
     * - Adds the step to {@link #kompilePaths}.
     * After running:
     * - Adds krun tasks that depend on this kompile step to the queue. (only if it's
     *   successfully done)
     * - Updates {@link #kompilePaths}.
     * @param kompileStep Kompile step to wrap.
     * @return New {@link java.lang.Runnable} that does things described above.
     */
    private Runnable wrapKompileStep(Proc<TestCase> kompileStep) {
        return new Runnable() {
            @Override
            public void run() {
                String kompilePath = kompileStep.getObj().getKompileDirFullPath();
                KompileStatus status = tryAddKompileInProgress(kompilePath);
                if (status == KompileStatus.NOT_STARTED) {
                    // We're running the kompile process
                    kompileStep.run();
                    boolean success = kompileStep.isSuccess();
                    synchronized (TaskQueue.this) {
                        kompilePaths.put(kompilePath,
                                success ? KompileStatus.SUCCEEDED : KompileStatus.FAILED);
                    }
                    addKRunSteps(kompileStep.getObj());
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
        };
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
     * Create a {@link java.lang.Runnable} from a kompile step that updates {@link #pdfDefs} after
     * it's done.
     * @param pdfStep PDF step to to wrap.
     * @return New {@link java.lang.Runnable} that does things described above.
     */
    private Runnable wrapPDFStep(Proc<TestCase> pdfStep) {
        return () -> {
            pdfStep.run();
            pdfDefs.put(pdfStep.getObj().getDefinition(), pdfStep.isSuccess());
        };
    }

    /**
     * Add KRun steps of the given test case to the {@link #tpe}.
     */
    private void addKRunSteps(TestCase tc) {

    }
}

