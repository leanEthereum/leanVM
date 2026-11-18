package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.lang.ref.Cleaner;
import java.util.Objects;
import java.util.function.Consumer;

/** Keeps an opaque native allocation alive for the duration of every FFM call using it. */
final class NativeHandle implements AutoCloseable {
    private static final Cleaner CLEANER = Cleaner.create();

    private final State state;
    private final Cleaner.Cleanable cleanable;

    NativeHandle(MemorySegment pointer, Consumer<MemorySegment> destroyer) {
        state = new State(pointer, destroyer);
        cleanable = CLEANER.register(this, state);
    }

    Borrow borrow() {
        return state.borrow();
    }

    @Override
    public void close() {
        cleanable.clean();
    }

    static final class Borrow implements AutoCloseable {
        private State state;
        private final MemorySegment pointer;

        private Borrow(State state, MemorySegment pointer) {
            this.state = state;
            this.pointer = pointer;
        }

        MemorySegment pointer() {
            return pointer;
        }

        @Override
        public void close() {
            if (state != null) {
                state.release();
                state = null;
            }
        }
    }

    private static final class State implements Runnable {
        private final Consumer<MemorySegment> destroyer;
        private MemorySegment pointer;
        private int borrows;
        private boolean closeRequested;

        private State(MemorySegment pointer, Consumer<MemorySegment> destroyer) {
            this.pointer = Objects.requireNonNull(pointer, "pointer");
            this.destroyer = Objects.requireNonNull(destroyer, "destroyer");
        }

        synchronized Borrow borrow() {
            if (closeRequested) {
                throw new IllegalStateException("native object is closed");
            }
            borrows++;
            return new Borrow(this, pointer);
        }

        synchronized void release() {
            borrows--;
            if (closeRequested && borrows == 0) {
                destroy();
            }
        }

        @Override
        public synchronized void run() {
            closeRequested = true;
            if (borrows == 0) {
                destroy();
            }
        }

        private void destroy() {
            if (pointer.address() != 0) {
                destroyer.accept(pointer);
                pointer = MemorySegment.NULL;
            }
        }
    }
}
