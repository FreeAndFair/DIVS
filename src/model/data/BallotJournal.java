package model.data;

import java.io.Serializable;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class BallotJournal implements Serializable {

	private static final long serialVersionUID = 1L;

	private int bj_id, total_votes, party_votes, personal_votes;
	private Party party;
	private Candidate candidate;

	//@ invariant bj_id > 0;
	//@ invariant party != null ^ candidate != null;
	//@ invariant party != null ==> personal_votes == 0;
	//@ invariant party_votes >= 0;
	//@ invariant personal_votes >= 0;
	//@ invariant total_votes == party_votes + personal_votes;

	//@ pre bj_id > 0;
	public BallotJournal(/*@ non_null @*/ Party p, int bj_id) {
		this.bj_id = bj_id;
		this.party = p;
		this.party_votes = 0;
		this.personal_votes = 0;
		this.total_votes = 0;
	}

	//@ pre bj_id > 0;
	public BallotJournal(/*@ non_null @*/ Candidate c, int bj_id) {
		this.bj_id = bj_id;
		this.candidate = c;
		this.party_votes = 0;
		this.personal_votes = 0;
		this.total_votes = 0;
	}

	/**
	 * @return The bj_id of the ballot journal (in the database)
	 */
	public /*@ pure @*/ int getBjId() {
		return bj_id;
	}

	/**
	 * @return the party
	 */
	public /*@ pure @*/ Party getParty() {
		return party;
	}

	/**
	 * @return the candidate
	 */
	public /*@ pure @*/ Candidate getCandidate() {
		return candidate;
	}

	/**
	 * @return the total_votes
	 */
	public /*@ pure @*/ int getTotalVotes() {
		return total_votes;
	}

	/**
	 * @return The number of votes the party xor candidate has got
	 */
	public /*@ pure @*/ int getPartyVotes() {
		return this.party_votes;
	}

	/**
	 * @return the personal_votes_int
	 */
	public /*@ pure @*/ int getPersonalVotes() {
		return personal_votes;
	}

	/**
	 * @param v The no of votes
	 */
	//@ pre v >= 0;
	//@ post party_votes == v;
	//@ assignable party_votes;
	public void setPartyVotes(int v) {
		this.party_votes = v;
		this.total_votes = party_votes + personal_votes;
	}
	
	/**
	 * @param v The no of personal votes
	 */
	//@ pre v >= 0;
	//@ post personal_votes == v;
	//@ assignable personal_votes;
	public void setPersonalVotes(int v) {
		this.personal_votes = v;
		this.total_votes = party_votes + personal_votes;
	}
	
	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "BallotJournal - "+(party != null ? "party":"candidate")+": "+(party != null ? party.getName():candidate.getName())+";total votes: "+total_votes+";party votes: "+party_votes+";personal_votes: "+personal_votes;
	}

}