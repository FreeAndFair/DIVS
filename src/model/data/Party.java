package model.data;

import java.io.Serializable;

import model.ElectionConstants;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Party implements Serializable {

	private static final long serialVersionUID = 1L;

	private int party_id;
	private String name, letter;
	private int list_organization;
	
	//@ invariant party_id > 0;
	//@ invariant name != null;
	//@ invariant letter != null;
	//@ invariant list_organization == ElectionConstants.STANDING_BY_DISTRICT || list_organization == ElectionConstants.STANDING_IN_PARALLEL;

	/**
	 * @param party_id Party_id in the database
	 * @param name Name of the party
	 * @param letter Party's letter
	 * @param standing How the party 'stands'
	 */
	//@ pre party_id > 0;
	//@ pre list_org == ElectionConstants.STANDING_BY_DISTRICT || list_org == ElectionConstants.STANDING_IN_PARALLEL;
	public Party(int party_id, /*@ non_null @*/ String name, 
			/*@ non_null @*/ String letter, int list_org) {
		this.party_id = party_id;
		this.name = name;
		this.letter = letter;
		this.list_organization = list_org;
	}
	
	/**
	 * @return The party id of the party (in the database)
	 */
	public /*@ pure @*/ int getPartyId() {
		return party_id;
	}
	
	/**
	 * @return The name of the party
	 */
	public /*@ pure @*/ String getName() {
		return name;
	}
	
	/**
	 * @return The (party) letter of the party
	 */
	public /*@ pure @*/ String getLetter() {
		return letter;
	}

	/**
	 * @return The standing (or principal form) that the party chooses to use
	 */
	public /*@ pure @*/ int getListOrganization() {
		return list_organization;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		@SuppressWarnings("unused")
		int i = ElectionConstants.SEATS_DENMARK; //used to make the import come without a warning
		return "Party - name: "+name+";letter: "+letter+";list_org.: "+list_organization;
	}

}