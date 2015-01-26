package model.utils;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class DivsException extends Exception {

	private static final long serialVersionUID = 1L;

	/*
	 * Error constants. Each category of errors belongs to same 10s 
	 */
	public static final int ERROR = 10;
	public static final int ERROR_SQL = 20;
	public static final int IO_ERROR = 30;
	public static final int FILE_NOT_FOUND = 31;
	public static final int ACCESS_DENIED = 32;
	public static final int INVALID_VOTE = 40;
	public static final int INVALID_JOURNAL_STATE = 41;
	public static final int POLLING_STATION_NOT_IN_LIST = 42;
	public static final int FRAGMENTAL_VOTE = 43;
	public static final int INVALID_ELECTION_STATE = 50;
	public static final int NO_DB_CONNECTION = 60;
	public static final int DB_CLASS_NOT_FOUND = 61;
	
	public static final int ILLEGAL_INPUT = 70;
	public static final int NOT_YET_IMPLEMENTED = -1;

	private int errorNo;

	/**
	 * @param errorNo The error number
	 * @param message The error message
	 */
	public DivsException(int errorNo, /*@ non_null @*/ String message) {
		super(message);
		this.errorNo = errorNo; 
	}

	/**
	 * Returns the error number
	 * @return errorNo
	 */
	public int getErrorNo() {
		return this.errorNo;
	}

}
