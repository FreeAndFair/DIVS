package model;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class ElectionStatus {
	/*
	 * Outer state machine of the election
	 */
	public static final int BEFORE_ELECTION = 0;
	public static final int INITIALIZED = 1;
	public static final int ELECTION_OPEN = 2;
	public static final int ELECTION_CLOSED = 3;
	public static final int PRELIMINARY_COUNTING_COMPLETED = 4;
	public static final int PRELIMINARY_RESULTS_COMPUTED = 5;
	public static final int FINAL_COUNTING_COMPLETED = 6;
	public static final int FINAL_RESULTS_COMPUTED = 7;

	/*
	 * Inner state machine of the election (computing the result)
	 */
	public static final int BEFORE_COMPUTING = 0;
	public static final int STEP_1_DONE = 1;
	public static final int STEP_1_RESOLVED = 2;
	public static final int THRESHOLD_DETERMINED = 3;
	public static final int STEP_3_DONE = 4;
	public static final int STEP_3_RESOLVED = 5;
	public static final int STEP_4_DONE = 6;
	public static final int STEP_4_RESOLVED = 7;
	public static final int STEP_5_DONE = 8;
	public static final int STEP_5_RESOLVED = 9;
	public static final int STEP_6_DONE = 10;
	public static final int STEP_6_RESOLVED = 11;
	public static final int NO_PASSING_PARTIES = 12;

	/*
	 * Open status of polling stations
	 */
	public static final int PS_NOT_OPEN = 0;
	public static final int PS_OPEN = 1;
	public static final int PS_CLOSED = 2;

}