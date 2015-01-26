package national.data.computation;

import national.data.Candidate;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class CandidateResult {

	private Candidate candidate;
	private int total_votes, personal_votes, party_votes;
	private boolean draw, elected;

	//@ invariant candidate != null;
	//@ invariant total_votes == party_votes + personal_votes;
	//@ invariant party_votes >= 0;
	//@ invariant personal_votes >= 0;
	
	/**
	 * @param candidate
	 * @param total_votes
	 * @param personal_votes
	 * @param party_votes
	 */
	//@ post candidate != null;
	//@ post personal_votes == 0;
	//@ post party_votes == 0;
	//@ post total_votes == 0;
	//@ post !elected;
	public CandidateResult(/*@ non_null @*/ Candidate candidate) {
		this.candidate = candidate;
		this.personal_votes = 0;
		this.party_votes = 0;
		this.total_votes = personal_votes + party_votes;
		this.elected = false;
	}

	/**
	 * @return Is this instance a subject to a draw (or tie)
	 */
	public /*@ pure @*/ boolean isDraw() {
		return draw;
	}

	/**
	 * Returns true if candidate is elected to the parliament
	 * @return the elected
	 */
	public /*@ pure @*/ boolean isElected() {
		return elected;
	}

	/**
	 * @return The candidate to whom the votes belong
	 */
	public /*@ pure @*/ Candidate getCandidate() {
		return candidate;
	}

	/**
	 * @return The total votes of the candidate. I.e. personal votes 
	 * plus some party votes corresponding to party's standing
	 */
	public /*@ pure @*/ int getTotalVotes() {
		return total_votes;
	}

	/**
	 * @return The personal votes that the candidate has got
	 */
	public /*@ pure @*/ int getPersonalVotes() {
		return personal_votes;
	}

	/**
	 * @return The party votes that the candidate has got
	 */
	public /*@ pure @*/ int getPartyVotes() {
		return party_votes;
	}

	/**
	 * @param draw The draw value to be set
	 */
	//@ post draw == d;
	//@ assignable draw;
	public void setDraw(boolean d) {
		this.draw = d;
	}

	/**
	 * @param votes_personal The personal votes to be set
	 */
	//@ pre p_votes_pers >= 0;
	//@ assignable personal_votes, total_votes;
	public void setPersonalVotes(int p_votes_pers) {
		this.personal_votes = p_votes_pers;
		this.total_votes = personal_votes + party_votes;
	}
	
	/**
	 * @return party_votes The party votes to be set
	 */
	//@ pre p_party_votes >= 0;
	//@ assignable party_votes, total_votes;
	public void setPartyVotes(int p_party_votes) {
		this.party_votes = p_party_votes;
		this.total_votes = party_votes + personal_votes;
	}

	/**
	 * When everything is computed then this method is called if candidate is elected 
	 */
	//@ post elected == e;
	//@ assignable elected;
	public void setElected(boolean e) {
		this.elected = e;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "CandidateResult - candidate: "+candidate.getName()+";total votes: "+total_votes+";party votes: "+party_votes+";personal_votes: "+personal_votes;
	}

}