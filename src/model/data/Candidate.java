package model.data;

import java.io.Serializable;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Candidate implements Serializable {

	private static final long serialVersionUID = 1L;

	private int candidate_id;
	private Party party;
	private String name, cpr, position, address;

	//@ invariant candidate_id > 0;
	//@ invariant name != null;
	//@ invariant cpr != null;
	//@ invariant position != null;
	//@ invariant address != null;

	/**
	 * @param candidate_id Id of candidate in database
	 * @param party Party to which candidate belongs
	 * @param name Name of candidate
	 * @param sex Sex of candidate
	 */
	//@ pre candidate_id > 0;
	//@ post party == p;
	public Candidate(int candidate_id, /*@ non_null @*/ String name,
			/*@ non_null @*/ String cpr, /*@ non_null @*/ Party p, 
			/*@ non_null @*/ String position, /*@ non_null @*/ String address) {
		this.candidate_id = candidate_id;
		this.name = name;
		this.cpr = cpr;
		this.position = position;
		this.address = address;
		this.party = p;
	}

	/**
	 * @return The candidate id of the candidate (in the database)
	 */
	public /*@ pure @*/ int getCandidateId() {
		return candidate_id;
	}

	/**
	 * @return The name of the candidate
	 */
	public /*@ pure @*/ String getName() {
		return this.name;
	}

	/**
	 * @return the cpr
	 */
	public /*@ pure @*/ String getCpr() {
		return cpr;
	}

	/**
	 * @return the position
	 */
	public /*@ pure @*/ String getPosition() {
		return position;
	}

	/**
	 * @return the address
	 */
	public /*@ pure @*/ String getAddress() {
		return address;
	}

	/**
	 * @return The party to which the candidate belongs
	 */
	public /*@ pure @*/ Party getParty() {
		return this.party;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "Candidate - name: "+name+";party: "+party.getName()+";cpr: "+cpr+";position: "+position+";address: "+address;
	}

}