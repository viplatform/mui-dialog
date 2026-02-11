import { useState } from "react";
import type { Meta, StoryObj } from "@storybook/react";
import MuiDialog from "../muiDialog";
import {
  MODAL_TYPES,
  MODAL_SIZES,
  INFORMATION_SUBTYPES,
  CONFIRMATION_SUBTYPES,
  INPUT_SUBTYPES,
  TERTIARY_CTA_TYPES,
} from "../muiDialog/constants/muiDialog.types";
import { Button } from "@mui/material";
import type {
  InformationModalProps,
  ConfirmationModalProps,
  InputModalProps,
} from "../muiDialog/constants/muiDialog.interfaces";

type ModalProps =
  | InformationModalProps
  | ConfirmationModalProps
  | InputModalProps;

const meta = {
  title: "Components/MuiDialog",
  component: MuiDialog,
  parameters: {
    layout: "centered",
    docs: {
      description: {
        component: `
# MuiDialog Component

A reusable dialog component for React applications built with Material-UI (MUI). This component provides various types of dialogs for different use cases:

## Types of Dialogs

1. **Information Dialog**
   - Used for displaying information to users
   - Supports different subtypes: acknowledgement, progress, and passive
   - Can include primary and secondary actions

2. **Confirmation Dialog**
   - Used for confirming user actions
   - Supports different subtypes: default, destructive, and nested
   - Always includes primary and secondary actions

3. **Input Dialog**
   - Used for collecting user input
   - Supports different subtypes: default and destructive
   - Can include form elements in the children prop

## Features

- Responsive design
- Support for primary, secondary, and tertiary actions
- Optional close icon
- Optional divider
- Customizable content through children prop
- Theme support

## Usage

\`\`\`tsx
import { MuiDialog } from 'mui-dialog';

// Basic usage
<MuiDialog
  open={true}
  type="information"
  subtype="passive"
  title="Dialog Title"
  description="Dialog description"
  onClose={() => {}}
  actions={{
    primaryCtaTitle: "Confirm",
    secondaryCtaTitle: "Cancel",
    onPrimaryCtaClick: () => {},
    onSecondaryCtaClick: () => {},
  }}
>
  <div>Additional content</div>
</MuiDialog>
\`\`\`
        `,
      },
    },
  },
  argTypes: {
    wrapperClassName: {
      control: "text",
      description: "Custom class name for the dialog wrapper",
    },
    subtype: {
      control: "select",
      options: [
        INFORMATION_SUBTYPES.ACKNOWLEDGEMENT,
        INFORMATION_SUBTYPES.PROGRESS,
        INFORMATION_SUBTYPES.PASSIVE,
      ],
    },
    tertiaryCtaType: {
      control: "select",
      options: Object.values(TERTIARY_CTA_TYPES),
      description: "Type of tertiary CTA button",
    },
    actions: {
      control: "object",
      description: "Action buttons configuration",
      table: {
        type: {
          summary: "IActions",
          detail: `
{
  primaryCtaTitle?: string;
  secondaryCtaTitle?: string;
  isPrimaryCtaLoading?: boolean;
  isPrimaryCtaDisabled?: boolean;
  isSecondaryCtaDisabled?: boolean;
  isSecondaryCtaLoading?: boolean;
  onPrimaryCtaClick?: () => void;
  onSecondaryCtaClick?: () => void;
  tertiaryCtaTitle?: string;
  tertiaryCtaStartIcon?: React.ReactNode;
  isTertiaryCtaLoading?: boolean;
  isTertiaryCtaDisabled?: boolean;
  onTertiaryCtaClick?: () => void;
}`,
        },
      },
    },
  },
  tags: ["autodocs"],
} satisfies Meta<typeof MuiDialog>;

export default meta;
type Story = StoryObj<typeof meta>;

// Information Modal Story
export const InformationModal: Story = {
  render: (args) => {
    const [open, setOpen] = useState(false);
    return (
      <>
        <Button variant="contained" onClick={() => setOpen(true)}>
          Open Information Dialog
        </Button>
        <MuiDialog
          {...args}
          open={open}
          onClose={() => setOpen(false)}
          actions={{
            ...args.actions,
            onPrimaryCtaClick: () => {
              console.log("Primary CTA clicked");
              setOpen(false);
            },
            onSecondaryCtaClick: () => {
              console.log("Secondary CTA clicked");
              setOpen(false);
            },
          }}
        />
      </>
    );
  },
  args: {
    open: false,
    onClose: () => {},
    type: MODAL_TYPES.INFORMATION,
    subtype: INFORMATION_SUBTYPES.PASSIVE,
    title: "Information Dialog",
    subTitle: "This is a subtitle",
    description:
      "This is a description of the information dialog. It can contain multiple lines of text to explain the purpose of the dialog.",
    showActions: true,
    showDivider: true,
    showCloseIcon: true,
    wrapperClassName: "",
    paperClassName: "",
    tertiaryCtaType: TERTIARY_CTA_TYPES.DEFAULT,
    children: <div>Additional content can go here</div>,
    actions: {
      primaryCtaTitle: "Confirm",
      secondaryCtaTitle: "Cancel",
      isPrimaryCtaLoading: false,
      isPrimaryCtaDisabled: false,
      isSecondaryCtaDisabled: false,
      isSecondaryCtaLoading: false,
      tertiaryCtaTitle: "",
      tertiaryCtaStartIcon: null,
      isTertiaryCtaLoading: false,
      isTertiaryCtaDisabled: false,
    },
  },
  parameters: {
    docs: {
      description: {
        story: "A basic information dialog with primary and secondary actions.",
      },
    },
  },
};

// Confirmation Modal Story
export const ConfirmationModal: Story = {
  render: (args) => {
    const [open, setOpen] = useState(false);
    return (
      <>
        <Button variant="contained" onClick={() => setOpen(true)}>
          Open Confirmation Dialog
        </Button>
        <MuiDialog
          {...args}
          open={open}
          onClose={() => setOpen(false)}
          actions={{
            ...args.actions,
            onPrimaryCtaClick: () => {
              console.log("Confirmed");
              setOpen(false);
            },
            onSecondaryCtaClick: () => {
              console.log("Cancelled");
              setOpen(false);
            },
          }}
        />
      </>
    );
  },
  args: {
    open: false,
    onClose: () => {},
    type: MODAL_TYPES.CONFIRMATION,
    subtype: CONFIRMATION_SUBTYPES.DEFAULT,
    title: "Confirmation Dialog",
    description: "Are you sure you want to proceed with this action?",
    showActions: true,
    showDivider: true,
    showCloseIcon: true,
    wrapperClassName: "",
    tertiaryCtaType: TERTIARY_CTA_TYPES.DEFAULT,
    children: <div>Additional confirmation details can go here</div>,
    actions: {
      primaryCtaTitle: "Yes, Proceed",
      secondaryCtaTitle: "No, Cancel",
      isPrimaryCtaLoading: false,
      isPrimaryCtaDisabled: false,
      isSecondaryCtaDisabled: false,
      isSecondaryCtaLoading: false,
      tertiaryCtaTitle: "",
      tertiaryCtaStartIcon: null,
      isTertiaryCtaLoading: false,
      isTertiaryCtaDisabled: false,
    },
  },
  argTypes: {
    subtype: {
      control: "select",
      options: [
        CONFIRMATION_SUBTYPES.DEFAULT,
        CONFIRMATION_SUBTYPES.DESTRUCTIVE,
        CONFIRMATION_SUBTYPES.NESTED,
      ],
    },
  },
  parameters: {
    docs: {
      description: {
        story: "A confirmation dialog used for confirming user actions.",
      },
    },
  },
};

// Destructive Confirmation Modal Story
export const DestructiveConfirmationModal: Story = {
  render: (args) => {
    const [open, setOpen] = useState(false);
    return (
      <>
        <Button variant="contained" onClick={() => setOpen(true)}>
          Open Destructive Dialog
        </Button>
        <MuiDialog
          {...args}
          open={open}
          onClose={() => setOpen(false)}
          actions={{
            ...args.actions,
            onPrimaryCtaClick: () => {
              console.log("Deleted");
              setOpen(false);
            },
            onSecondaryCtaClick: () => {
              console.log("Cancelled");
              setOpen(false);
            },
          }}
        />
      </>
    );
  },
  args: {
    open: false,
    onClose: () => {},
    type: MODAL_TYPES.CONFIRMATION,
    subtype: CONFIRMATION_SUBTYPES.DESTRUCTIVE,
    title: "Delete Confirmation",
    description:
      "Are you sure you want to delete this item? This action cannot be undone.",
    showActions: true,
    showDivider: true,
    showCloseIcon: true,
    wrapperClassName: "",
    tertiaryCtaType: TERTIARY_CTA_TYPES.DEFAULT,
    children: <div>Additional warning details can go here</div>,
    actions: {
      primaryCtaTitle: "Delete",
      secondaryCtaTitle: "Cancel",
      isPrimaryCtaLoading: false,
      isPrimaryCtaDisabled: false,
      isSecondaryCtaDisabled: false,
      isSecondaryCtaLoading: false,
      tertiaryCtaTitle: "",
      tertiaryCtaStartIcon: null,
      isTertiaryCtaLoading: false,
      isTertiaryCtaDisabled: false,
    },
  },
  parameters: {
    docs: {
      description: {
        story:
          "A destructive confirmation dialog used for dangerous actions like deletion.",
      },
    },
  },
};

// Input Modal Story
export const InputModal: Story = {
  render: (args) => {
    const [open, setOpen] = useState(false);
    return (
      <>
        <Button variant="contained" onClick={() => setOpen(true)}>
          Open Input Dialog
        </Button>
        <MuiDialog
          {...args}
          open={open}
          onClose={() => setOpen(false)}
          actions={{
            ...args.actions,
            onPrimaryCtaClick: () => {
              console.log("Submitted");
              setOpen(false);
            },
            onSecondaryCtaClick: () => {
              console.log("Cancelled");
              setOpen(false);
            },
          }}
        />
      </>
    );
  },
  args: {
    open: false,
    onClose: () => {},
    type: MODAL_TYPES.INPUT,
    subtype: INPUT_SUBTYPES.DEFAULT,
    title: "Input Dialog",
    description: "Please provide the required information below:",
    showActions: true,
    showDivider: true,
    showCloseIcon: true,
    wrapperClassName: "",
    tertiaryCtaType: TERTIARY_CTA_TYPES.DEFAULT,
    actions: {
      primaryCtaTitle: "Submit",
      secondaryCtaTitle: "Cancel",
      isPrimaryCtaLoading: false,
      isPrimaryCtaDisabled: false,
      isSecondaryCtaDisabled: false,
      isSecondaryCtaLoading: false,
      tertiaryCtaTitle: "",
      tertiaryCtaStartIcon: null,
      isTertiaryCtaLoading: false,
      isTertiaryCtaDisabled: false,
    },
    children: (
      <div style={{ padding: "16px 0" }}>
        <p>Your input form content goes here</p>
      </div>
    ),
  },
  argTypes: {
    subtype: {
      control: "select",
      options: [INPUT_SUBTYPES.DEFAULT, INPUT_SUBTYPES.DESTRUCTIVE],
    },
  },
  parameters: {
    docs: {
      description: {
        story: "An input dialog used for collecting user input.",
      },
    },
  },
};
