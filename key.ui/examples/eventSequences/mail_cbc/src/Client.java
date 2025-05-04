public final class Client {
    private String inbox = "";

    public void encrypt(Mail mail) { mail.isEncrypted = true; }

    public void decrypt(Mail mail) {
        mail.isEncrypted = false;
    }

    public void addToInbox(Mail mail) {
        inbox += mail.content;
    }

    public void send(Client receiver, Mail mail) {
        // Some code to send the mail
    }

    public void forward(Client receiver, Mail mail) {
        decrypt(mail);
        addToInbox(mail);
        send(receiver, mail);
    }
}