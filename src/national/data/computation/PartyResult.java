package national.data.computation;

import java.util.ArrayList;
import java.util.List;
import national.ElectionConstants;
import national.data.Party;

/**
 * @author Ólavur Kjølbro
 * Class is used when all party votes are accumulated on constituency
 * level and on national level.
 */
public /*@ nullable_by_default @*/ class PartyResult {

	private Party party;
	private boolean threshold_passed;
	private int total_votes, no_of_elected, method;
	private int total_seats, constituency_seats, additional_seats, additional_seats_taken;
	private boolean draw;
	private List<Div> divs;
	private List<CandidateResult> candidate_results;

	//@ invariant party != null;
	//@ invariant candidate_results != null;
	//@ invariant total_votes >= 0;
	//@ invariant total_seats == constituency_seats + additional_seats;
	//@ invariant total_seats >= 0;
	//@ invariant constituency_seats >= 0;
	//@ invariant no_of_elected >= 0;

	/**
	 * @param p Party
	 */
	//@ post candidate_results != null;
	//@ post no_of_elected == 0;
	//@ post !threshold_passed;
	//@ post party == p;
	//@ post total_seats == 0;
	//@ post constituency_seats == 0;
	//@ post additional_seats == 0;
	public PartyResult(/*@ non_null @*/ Party p, int m) {
		this.party = p;
		this.method = m;
		this.threshold_passed = false;
		this.total_votes = 0;
		this.total_seats = 0;
		this.constituency_seats = 0;
		this.additional_seats = 0;
		this.no_of_elected = 0;
		this.draw = false;
		this.candidate_results = new ArrayList<CandidateResult>();
		divs = new ArrayList<Div>();
	}

	/**
	 * @return the party
	 */
	public /*@ pure @*/ Party getParty() {
		return party;
	}

	/**
	 * @return the method
	 */
	public /*@ pure @*/ int getMethod() {
		return method;
	}

	/**
	 * @return the divs
	 */
	public /*@ pure @*/ List<Div> getDivs() {
		return divs;
	}

	/**
	 * @return The threshold_passed boolean value
	 */
	public /*@ pure @*/ boolean isThresholdPassed() {
		return threshold_passed;
	}
	
	protected boolean getShit() {
		return false;
	}

	/**
	 * @return The total no of votes
	 */
	public /*@ pure @*/ int getTotalVotes() {
		return total_votes;
	}

	/**
	 * @return The no of constituency seats that this party has got
	 */
	public /*@ pure @*/ int getConstituencySeats() {
		return constituency_seats;
	}

	/**
	 * @return The additional seats that this party has got
	 */
	public /*@ pure @*/ int getAdditionalSeats() {
		return additional_seats;
	}

	/**
	 * @return The total number of seats that this party has got
	 */
	public /*@ pure @*/ int getTotalSeats() {
		return total_seats;
	}

	/**
	 * @return the no_of_elected
	 */
	public /*@ pure @*/ int getNoOfElected() {
		return no_of_elected;
	}

	/**
	 * @return the additional_seats_taken
	 */
	public /*@ pure @*/ int getAdditionalSeatsTaken() {
		return additional_seats_taken;
	}

	/**
	 * @return If there is a draw that this party is involved in
	 */
	public /*@ pure @*/ boolean isDraw() {
		return draw;
	}

	/**
	 * @return If no of elected should be reduced later
	 */
	public /*@ pure @*/ boolean isResolved() {
		return no_of_elected == total_seats;
	}

	/**
	 * @return The list of personal votes
	 */
	public /*@ pure @*/ List<CandidateResult> getCandidateResults() {
		return candidate_results;
	}

	/**
	 * @param m The method to set
	 */
	//@ pre m == ElectionConstants.DHONDT || m == ElectionConstants.SAINTE_LAGUE || m == ElectionConstants.DANISH_METHOD;
	//@ post method == m;
	//@ assignable method;
	public void setMethod(int m) {
		this.method = m;
	}
	
	/**
	 * @param no_of_elected the no_of_elected to set
	 */
	//@ pre no >= 0;
	//@ post no_of_elected == no;
	//@ assignable no_of_elected;
	public void setNoOfElected(int no) {
		this.no_of_elected = no;
	}

	/**
	 * @param pers_votes the pers_votes to set
	 */
	public void setCandidateResults(List<CandidateResult> cand_res) {
		this.candidate_results = cand_res;
	}

	/**
	 * @param passed_value The threshold_passed boolean value
	 */
	//@ post threshold_passed == passed_value;
	//@ assignable threshold_passed; 
	public void setThresholdPassed(boolean passed_value) {
		this.threshold_passed = passed_value;
	}

	/**
	 * @param v No of votes to be added to current
	 */
	//@ pre v >= 0;
	//@ post total_votes == v;
	//@ assignable total_votes; 
	public void setTotalVotes(int v) {
		this.total_votes = v;
	}
	
	/**
	 * Method sets the constituency seats and then updates the total 
	 * number of seats
	 * @param constit_seats The constituency_seats to be set
	 */
	//@ pre constit_seats >= 0;
	//@ post constituency_seats == constit_seats;
	//@ assignable constituency_seats, total_seats;
	public void setConstituencySeats(int constit_seats) {
		this.constituency_seats = constit_seats;
		this.total_seats = constituency_seats + additional_seats;
	}

	/**
	 * Method sets the additional seats and then updates the total
	 * number of seats. Number of additional seats might be negative,
	 * but the lower bound is the value that makes the total number
	 * of seats negative.
	 * @param addit_seats the additional_seats to set
	 */
	//@ pre addit_seats >= constituency_seats * (-1);
	//@ post additional_seats == addit_seats;
	//@ assignable total_seats, additional_seats; 
	public void setAdditionalSeats(int addit_seats) {
		this.additional_seats = addit_seats;
		this.total_seats = constituency_seats + additional_seats;
	}

	/**
	 * @param additional_seats_taken the additional_seats_taken to set
	 */
	//@ pre seats_taken >= 0;
	//@ post additional_seats_taken == seats_taken;
	//@ assignable additional_seats_taken; 
	public void setAdditionalSeatsTaken(int seats_taken) {
		this.additional_seats_taken = seats_taken;
	}

	/**
	 * Method sets the total seats and then updates the
	 * additional seats, since the additional seats are 
	 * always set after the constituency seats 
	 * @param seats_total the total_seats to set
	 */
	//@ pre seats_total >= 0;
	//@ pre seats_total >= constituency_seats;
	//@ post total_seats == seats_total;
	//@ post additional_seats == total_seats - constituency_seats;
	//@ assignable total_seats, additional_seats; 
	public void setTotalSeats(int seats_total) {
		this.total_seats = seats_total;
		this.additional_seats = total_seats - constituency_seats; 
	}

	/**
	 * @param d Sets the 'draw' attribute of the party result
	 */
	//@ post draw == d;
	//@ assignable draw; 
	public void setDraw(boolean d) {
		this.draw = d;
	}

	/**
	 * Add one Div instance to divs list
	 */
	//@ post divs.size() == \old(divs.size()) + 1;
	//@ assignable divs;
	public void addOneToDivList() {
		double f = (double) ((double) total_votes / (double) (1+(divs.size()*method)));
		divs.add(new Div(this, f));
//		divs.add(new Div(this, total_votes, 1+(divs.size()*method)));
	}

	/**
	 * Method initializes the div list for step 4 and step 5 in the 
	 * computing process or the election's result 
	 */
	//@ post divs.size() == constituency_seats + 1;
	//@ assignable divs;
	public void createInitDivs() {
		divs.clear();
		for (int i = 0; i < (this.constituency_seats + 1); i++) {
//			divs.add(new Div(this, total_votes / 
//			(1 + (divs.size() * method))));
//			divs.add(new Div(this, total_votes, 1 + (divs.size() * method)));
			addOneToDivList();
		}
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "PartyResult - party: "+party.getName()+";total votes: "+total_votes+";threshold passed: "+threshold_passed+";constituency seats: "+constituency_seats+";additional seats: "+additional_seats+";draw: "+draw+";no of elected: "+no_of_elected+";pers votes size: "+candidate_results.size();
	}
}