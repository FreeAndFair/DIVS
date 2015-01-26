package model.data.computation;

import java.util.ArrayList;
import java.util.List;

import model.data.map.Constituency;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class ConstituencyResult {

	private Constituency constituency;
	private List<PartyResult> party_results;
	private List<CandidateResult> independent_candidates;
	private int seats_taken;
	private int invalid_votes;
	private int electable_independent_candidates;

	//@ invariant constituency != null;
	//@ invariant party_results != null;
	//@ invariant seats_taken >= 0;
	//@ invariant independent_candidates != null;
	//@ invariant electable_independent_candidates >= 0;	

	/**
	 * @param constituency Constituency
	 */
	public ConstituencyResult(/*@ non_null @*/ Constituency constituency) {
		this.constituency = constituency;
		party_results = new ArrayList<PartyResult>();
		independent_candidates = new ArrayList<CandidateResult>();
		seats_taken = 0;
		invalid_votes = 0;
		electable_independent_candidates = 0;
	}
	
	/**
	 * @return the constituency
	 */
	//@ assignable \nothing;
	public /*@ pure @*/ Constituency getConstituency() {
		return constituency;
	}

	/**
	 * @return The list of PartyResult
	 */
	//@ assignable \nothing;
	public /*@ pure @*/ List<PartyResult> getPartyResult() {
		return party_results;
	}

	/**
	 * @return the independent_candidates
	 */
	public /*@ pure @*/ List<CandidateResult> getIndependentCandidates() {
		return independent_candidates;
	}

	/**
	 * @return the seats_taken
	 */
	public /*@ pure @*/ int getSeatsTaken() {
		return seats_taken;
	}

	/**
	 * @return the invalid_votes
	 */
	public /*@ pure @*/ int getInvalidVotes() {
		return invalid_votes;
	}

	/**
	 * @return the electable_indep_cand
	 */
	public /*@ pure @*/ int getElectableIndependentCandidates() {
		return electable_independent_candidates;
	}

	/**
	 * @param invalid_votes the invalid_votes to set
	 */
	public void setInvalidVotes(int inv_votes) {
		this.invalid_votes = inv_votes;
	}

	/**
	 * @param seats_taken the seats_taken to set
	 */
	//@ pre seats >= 0;
	//@ post seats_taken == seats;
	//@ assignable seats_taken;
	public void setSeatsTaken(int seats) {
		this.seats_taken = seats;
	}

	/**
	 * @return the independent_candidates
	 */
	public void setIndependentCandidates(List<CandidateResult> indep_cand) {
		this.independent_candidates = indep_cand;
	}

	/**
	 * @return the party_results
	 */
	public void setPartyResult(List<PartyResult> party_res) {
		this.party_results = party_res;
	}

	/**
	 * Method creates the inititial divisor list for all parties in a 
	 * certain constituency according to a certain divisor method e.g.
	 * d'Hondt. Since all first divisors are 1 the value of first Div
	 * is always votes divided by 1  
	 */
	//@ post (\forall int j; 0 <= j && j < party_results.size(); party_results.get(j).getDivs().size() == 1);
	//@ assignable party_results;
	public void createInitDivisorList() {
		PartyResult pres;
		for (int j = 0; j < party_results.size(); j++) {
			pres = party_results.get(j);
			pres.getDivs().clear();
			pres.addOneToDivList();
		}
	}
	
	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "ConstituencyResult - constituency: "+constituency.getName()+";seats taken: "+seats_taken+";party result size: "+party_results.size()+";independent candidates size: "+independent_candidates.size();
	}

	/**
	 * @param counter Number of electable independent candidates
	 */
	//@ pre counter >= 0;
	//@ post electable_independent_candidates == counter;
	public void setElectableIndpendentCandidates(int counter) {
		this.electable_independent_candidates = counter;
	}

}