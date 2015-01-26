package national.data.computation;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Div {

	private PartyResult pres;
	private CandidateResult cres;
	//private BigDecimal quotient;
	private double quotient;
	private int ranking;

	//@ invariant cres != null ^ cres != null;
	//@ invariant quotient != null;
	//@ invariant ranking >= 0;

	/**
	 * @param vp Votes party
	 * @param value The value of this div
	 */
	//@ pre q >= 0;
	public Div(/*@ non_null @*/ PartyResult p, double q) {
		this.pres = p;
//		BigDecimal dividend = BigDecimal.valueOf((long) p_dividend);
//		BigDecimal divisor = BigDecimal.valueOf((long) p_divisor);
//		quotient = dividend.divide(divisor);
		this.quotient = q;
		this.ranking = 0;
	}
	
	public Div(/*@ non_null @*/ CandidateResult cr) {
		this.cres = cr;
		//this.quotient = BigDecimal.valueOf((long) cres.getTotalVotes());
		this.quotient = cres.getTotalVotes();
	}
	
	/**
	 * @return The party (votes) belonging to div
	 */
	public /*@ pure @*/ PartyResult getPartyResult() {
		return pres;
	}

	/**
	 * @return The candidate result
	 */
	public /*@ pure @*/ CandidateResult getCandidateResult() {
		return cres;
	}

	/**
	 * @return The quotient of the div
	 */
	public /*@ pure @*/ double getQuotient() {
		return quotient;
	}

	/**
	 * @return the ranking
	 */
	public /*@ pure @*/ int getRanking() {
		return ranking;
	}

	/**
	 * @param ranking the ranking to set
	 */
	//@ pre rank >= 0;
	//@ post ranking == rank;
	//@ assignable ranking;
	public void setRanking(int rank) {
		this.ranking = rank;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "Div - party: "+pres.getParty().getName()+";quotient: "+quotient;
	}
}