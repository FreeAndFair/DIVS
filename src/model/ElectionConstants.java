package model;

/**
 * Class contains constants used throughout in the election.
 * 
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class ElectionConstants {
	/*
	 * Totals (limits)
	 */
	public static final int SEATS_TOTAL = 179;
	public static final int SEATS_FAROE_ISLANDS = 2;
	public static final int SEATS_GREENLAND = 2;
	public static final int SEATS_DENMARK = 175;
	public static final int ADDITIONAL_SEATS = 40;
	public static final int CONSTITUENCY_SEATS = 135;
	public static final int NO_OF_PROVINCES = 3;
	public static final int NO_OF_CONSTITUENCIES = 10;
	public static final int NO_OF_DISTRICTS = 92;

	/*
	 * Division methods
	 */
	public static final int DHONDT = 1;
	public static final int SAINTE_LAGUE = 2;
	public static final int DANISH_METHOD = 3;

	/*
	 * Parties can choose different standings
	 */
	public static final int STANDING_BY_DISTRICT = 1;
	public static final int STANDING_IN_PARALLEL = 2;

	/*
	 * Preliminary vs. final
	 */
	public static final int PRELIMINARY_ = 1;
	public static final int FINAL_ = 2;

}