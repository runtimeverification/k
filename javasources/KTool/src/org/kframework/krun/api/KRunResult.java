package org.kframework.krun.api;

import org.kframework.krun.K;

public class KRunResult<T> {
	private String statistics;
	private String rawOutput;
	private T result;

	public KRunResult(T result) {
		this.result = result;
	}

	public String getStatistics() {
		return statistics;
	}

	public void setStatistics(String statistics) {
		this.statistics = statistics;
	}

	public String getRawOutput() {
		return rawOutput;
	}

	public void setRawOutput(String rawOutput) {
		this.rawOutput = rawOutput;
	}

	public T getResult() {
		return result;
	}

	public void setResult(T result) {
		this.result = result;
	}

	@Override
	public String toString() {
		if (!K.statistics) {
			return result.toString();
		} else {
			return result.toString() + "\n" + statistics;
		}
	}
}
